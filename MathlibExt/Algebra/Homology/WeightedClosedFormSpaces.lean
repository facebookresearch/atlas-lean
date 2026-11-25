/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.GradedMixedCochainModels
public import MathlibExt.CategoryTheory.DGSourceMore.CochainToSSet
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Weighted negative-cyclic form spaces and their actual projection

For a genuine graded mixed complex G and its fixed NC-weight model,
the p-form space in degree n is the native Dold--Kan realization of
the good truncation of G(p)[n-p]. The closed-form space uses NC(G)(p)
with the same shift. Projection to the i=0 product coefficient is an
actual chain map, so it gives the actual underlying-form map.

Closed forms retain the full product-complex closing data. This is a
realization layer on a given graded mixed complex; identifying that
complex with derived de Rham of an algebra/stack is a separate normalized
construction, not an arbitrary label on G.

Reference: PTVV, arXiv:1111.3209v4, §1.1, Definitions 1.7--1.8.
The actual good truncation/Dold--Kan functor is completed source support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Algebra.Homology.WeightedClosedFormSpaces

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.DGSource

universe u

variable {k : Type u} [CommRing k]

/-- Literal projection onto the weight-p, i=0 product component. -/
def firstProjection (G : GradedMixed k) (p n : ℤ) : term G p n ⟶ (G.weight p).X n :=
  let f : term G p n ⟶ (G.weight (p + (0 : ℤ))).X (n - 2 * (0 : ℤ)) :=
    ModuleCat.ofHom (LinearMap.proj (R := k) (0 : ℕ))
  f ≫ eqToHom (by simp)

/-- The incoming mixed term is zero at i=0, giving a genuine projection of complexes. -/
theorem differential_first (G : GradedMixed k) (p n : ℤ) :
    differential G p n ≫ firstProjection G p (n + 1) =
      firstProjection G p n ≫ (G.weight p).d n (n + 1) := by
  have raw : differential G p n ≫
      ModuleCat.ofHom (LinearMap.proj (R := k) (0 : ℕ)) =
      ModuleCat.ofHom (LinearMap.proj (R := k) (0 : ℕ)) ≫
        (G.weight (p + (0 : ℤ))).d (n - 2 * (0 : ℤ))
          (n + 1 - 2 * (0 : ℤ)) := by
    ext x
    change _ + incoming G p n 0 x = _
    simp only [incoming, LinearMap.zero_apply, add_zero]
    rfl
  have natural := eqToHom_naturality
    (fun z : ℤ × ℤ × ℤ => (G.weight z.1).d z.2.1 z.2.2)
    (show (p + (0 : ℤ), n - 2 * (0 : ℤ), n + 1 - 2 * (0 : ℤ)) =
      (p, n, n + 1) by simp)
  dsimp only [firstProjection]
  rw [← Category.assoc, raw, Category.assoc, natural, ← Category.assoc]

/-- The actual underlying-form chain map of a normalized NC model. -/
def weightProjection {G : GradedMixed k} {p : ℤ} (M : NegativeCyclicModel G p) :
    M.complex ⟶ G.weight p where
  f n := (M.termIso n).hom ≫ firstProjection G p n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    rw [← Category.assoc, M.differential_eq]
    simp only [Category.assoc]
    rw [differential_first]

/-- The native underlying weighted p-form space with the source degree shift. -/
def formSpace (G : GradedMixed k) (p : ℕ) (n : ℤ) : SSet.{u} :=
  (cochainToSSet k).obj ((G.weight (p : ℤ))⟦n - (p : ℤ)⟧)

/-- The native closed p-form space retains every negative-cyclic product coefficient. -/
def closedFormSpace {G : GradedMixed k} (p : ℕ) (n : ℤ)
    (M : NegativeCyclicModel G (p : ℤ)) : SSet.{u} :=
  (cochainToSSet k).obj (M.complex⟦n - (p : ℤ)⟧)

/-- The actual underlying-form map is good truncation/Dold--Kan of the projection. -/
def underlyingForm {G : GradedMixed k} (p : ℕ) (n : ℤ)
    (M : NegativeCyclicModel G (p : ℤ)) : closedFormSpace p n M ⟶ formSpace G p n :=
  (cochainToSSet k).map
    ((shiftFunctor (CochainComplex (ModuleCat.{u} k) ℤ) (n - (p : ℤ))).map
      (weightProjection M))

/-- A closed form is an actual vertex of the closing-data space. -/
abbrev ClosedForm {G : GradedMixed k} (p : ℕ) (n : ℤ)
    (M : NegativeCyclicModel G (p : ℤ)) :=
  (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶ closedFormSpace p n M

/-- A given actual NC chain map induces its literal map on all form simplices. -/
def closedFormMap {G H : GradedMixed k} (p : ℕ) (n : ℤ)
    {M : NegativeCyclicModel G (p : ℤ)} {N : NegativeCyclicModel H (p : ℤ)}
    (g : M.complex ⟶ N.complex) : closedFormSpace p n M ⟶ closedFormSpace p n N :=
  (cochainToSSet k).map
    ((shiftFunctor (CochainComplex (ModuleCat.{u} k) ℤ) (n - (p : ℤ))).map g)

end MathlibExt.Algebra.Homology.WeightedClosedFormSpaces
