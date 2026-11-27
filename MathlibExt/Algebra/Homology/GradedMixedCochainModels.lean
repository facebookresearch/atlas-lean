/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.Pi

/-!
# Graded mixed complexes and their fixed negative-cyclic differential

The weight components are actual cochain complexes. The mixed operator is
a closed degree minus one cochain raising weight by one, and its square is
zero. The weighted negative-cyclic term is the actual product of the
components in degrees `n - 2*i`. Its differential is the internal
differential plus the incoming mixed differential. A normalized model has
these terms and this differential; no cohomology or spectral sequence is
supplied as unconstrained data.

References: Pantev--Toën--Vaquié--Vezzosi, arXiv:1111.3209v4, §1.1,
Definitions 1.7--1.8; Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1.
The cochain and Hom-complex operations used here are completed Mathlib
operations. The existence of the product cochain model is requested in a
separate Wanted module, without assuming degeneration or nondegeneracy.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.GradedMixedCochainModels

open CategoryTheory CochainComplex
open CochainComplex.HomComplex

universe u

variable (k : Type u) [CommRing k]

/-- An actual cohomological graded mixed complex; epsilon has degree -1
and increases weight by one. -/
structure GradedMixed where
  weight : ℤ → CochainComplex (ModuleCat.{u} k) ℤ
  epsilon : ∀ w : ℤ, Cochain (weight w) (weight (w + 1)) (-1)
  closed : ∀ w : ℤ, δ (-1) 0 (epsilon w) = 0
  square : ∀ w : ℤ,
    (epsilon w).comp (epsilon (w + 1)) (show (-1 : ℤ) + -1 = -2 by omega) = 0

variable {k}

/-- The actual product of weight pieces in the source negative-cyclic
degree convention. -/
abbrev Coefficients (G : GradedMixed k) (p n : ℤ) :=
  ∀ i : ℕ, (G.weight (p + (i : ℤ))).X (n - 2 * (i : ℤ))

/-- The native module object of the negative-cyclic degree. -/
def term (G : GradedMixed k) (p n : ℤ) : ModuleCat.{u} k :=
  ModuleCat.of k (Coefficients G p n)

/-- The incoming epsilon term. There is no incoming component at i=0. -/
def incoming (G : GradedMixed k) (p n : ℤ) (i : ℕ) :
    Coefficients G p n →ₗ[k] (G.weight (p + (i : ℤ))).X (n + 1 - 2 * (i : ℤ)) :=
  match i with
  | 0 => 0
  | j + 1 =>
    let t := (G.epsilon (p + (j : ℤ))).v
      (n - 2 * (j : ℤ)) (n + 1 - 2 * ((j + 1 : ℕ) : ℤ)) (by omega)
    let c : (G.weight ((p + (j : ℤ)) + 1)).X
        (n + 1 - 2 * ((j + 1 : ℕ) : ℤ)) ⟶
        (G.weight (p + ((j + 1 : ℕ) : ℤ))).X
        (n + 1 - 2 * ((j + 1 : ℕ) : ℤ)) :=
      eqToHom (by congr 2; omega)
    c.hom.comp (t.hom.comp (LinearMap.proj j))

/-- The fixed product differential d + u*epsilon. Its incoming component
and degree shifts are computed from the supplied mixed complex. -/
def differential (G : GradedMixed k) (p n : ℤ) : term G p n ⟶ term G p (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun x i =>
        (G.weight (p + (i : ℤ))).d (n - 2 * (i : ℤ))
          (n + 1 - 2 * (i : ℤ)) (x i) + incoming G p n i x
      map_add' := by
        intro x y
        funext i
        simp only [Pi.add_apply, map_add]
        abel
      map_smul' := by
        intro a x
        funext i
        simp only [Pi.smul_apply, map_smul, smul_add, RingHom.id_apply] }

/-- A cochain model is determined degreewise by the actual product and
the fixed mixed differential. The complex and comparison fields cannot
choose an unrelated cyclic invariant. -/
structure NegativeCyclicModel (G : GradedMixed k) (p : ℤ) where
  complex : CochainComplex (ModuleCat.{u} k) ℤ
  termIso : ∀ n : ℤ, complex.X n ≅ term G p n
  differential_eq : ∀ n : ℤ,
    complex.d n (n + 1) ≫ (termIso (n + 1)).hom =
      (termIso n).hom ≫ differential G p n

/-- A morphism of graded mixed complexes uses actual chain maps and
commutes with the actual epsilon cochains. -/
structure MixedMap (G H : GradedMixed k) where
  map : ∀ w : ℤ, G.weight w ⟶ H.weight w
  epsilon : ∀ (w a b : ℤ) (h : a + (-1 : ℤ) = b),
    (G.epsilon w).v a b h ≫ (map (w + 1)).f b =
      (map w).f a ≫ (H.epsilon w).v a b h

/-- The degreewise product map induced by a mixed-complex morphism. -/
def termMap {G H : GradedMixed k} (f : MixedMap G H) (p n : ℤ) :
    term G p n ⟶ term H p n :=
  ModuleCat.ofHom
    { toFun := fun x i => (f.map (p + (i : ℤ))).f (n - 2 * (i : ℤ)) (x i)
      map_add' := by intro x y; funext i; exact map_add _ _ _
      map_smul' := by intro a x; funext i; exact map_smul _ _ _ }

/-- The normalized cochain-map input type. Its map is specified on every
actual degree, not by an assumed cohomology comparison. -/
def IsNegativeCyclicMap {G H : GradedMixed k} (f : MixedMap G H) (p : ℤ)
    (M : NegativeCyclicModel G p) (N : NegativeCyclicModel H p)
    (g : M.complex ⟶ N.complex) : Prop :=
  ∀ n : ℤ, g.f n ≫ (N.termIso n).hom =
    (M.termIso n).hom ≫ termMap f p n

end MathlibExt.Algebra.Homology.GradedMixedCochainModels
