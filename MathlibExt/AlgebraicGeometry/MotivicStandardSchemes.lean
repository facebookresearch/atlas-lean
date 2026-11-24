/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Standard affine, torus and algebraic-simplex geometry for motivic cycles

Affine spaces are spectra of their actual polynomial rings. Tori are spectra
of the actual group algebras of Z^q, and unit insertion deletes that exponent
coordinate. The algebraic simplex has coordinate relation sum x_i = 1;
every ordinal map sends x_j to the sum of x_i with image j.

The chosen smooth presentations are normalized by scheme isomorphisms and
whole Spec maps. The affine origin and its open complement retain the actual
closed origin rather than a topological or arbitrary replacement sphere.

Sources: Mazza--Voevodsky--Weibel, Definitions 2.12--2.14 and 3.1;
Voevodsky arXiv:math/0107109v1, §2 and §5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicStandardSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open scoped Simplicial

variable {k : Type} [Field k]

abbrev affineRing (k : Type) [Field k] (q : ℕ) := MvPolynomial (Fin q) k
abbrev torusRing (k : Type) [Field k] (q : ℕ) := AddMonoidAlgebra k (Fin q → ℤ)

def simplexRelation (k : Type) [Field k] (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) k) :=
  Ideal.span {(∑ i : Fin (n + 1), MvPolynomial.X i) - (1 : MvPolynomial (Fin (n + 1)) k)}

abbrev simplexRing (k : Type) [Field k] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) k ⧸ simplexRelation k n

def simplexVariable (k : Type) [Field k] (n : ℕ) (i : Fin (n + 1)) : simplexRing k n :=
  Ideal.Quotient.mk (simplexRelation k n) (MvPolynomial.X i)

/-- All coordinate ring maps of the algebraic simplex are fixed on actual generators. -/
structure SimplexRingMaps (k : Type) [Field k] where
  map : ∀ {m n : SimplexCategory}, (m ⟶ n) → simplexRing k n.len →ₐ[k] simplexRing k m.len
  variable_eq : ∀ {m n : SimplexCategory} (a : m ⟶ n) (j : Fin (n.len + 1)),
    map a (simplexVariable k n.len j) =
      ∑ i : Fin (m.len + 1), if a.toOrderHom i = j then simplexVariable k m.len i else 0

/-- Unit insertion sets the selected invertible coordinate equal to one. -/
structure TorusRingMaps (k : Type) [Field k] where
  insert : ∀ (q : ℕ) (i : Fin (q + 1)), torusRing k (q + 1) →ₐ[k] torusRing k q
  monomial_eq : ∀ (q : ℕ) (i : Fin (q + 1)) (v : Fin (q + 1) → ℤ) (a : k),
    insert q i (AddMonoidAlgebra.single v a) =
      AddMonoidAlgebra.single (fun j : Fin q => v (i.succAbove j)) a

/-- Actual standard schemes and their source-normalized maps. -/
structure StandardSchemes (P : SmoothProductSystem k) where
  affine : ℕ → SmoothScheme k
  affineIso : ∀ q : ℕ, (affine q).scheme.left ≅ Spec (.of (affineRing k q))
  affine_base : ∀ q : ℕ, (affine q).scheme.hom =
    (affineIso q).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing k q)))
  zero : ∀ q : ℕ, P.unit ⟶ affine q
  zero_eq : ∀ q : ℕ, P.unitIso.inv ≫ (zero q).left ≫ (affineIso q).hom =
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin q => 0)))
  complement : ℕ → SmoothScheme k
  complementInclusion : ∀ q : ℕ, complement q ⟶ affine q
  open_immersion : ∀ q : ℕ, IsOpenImmersion (complementInclusion q).left
  complement_eq : ∀ q : ℕ,
    Set.range (complementInclusion q).left = (Set.range (zero q).left)ᶜ
  firstProjection : ∀ q r : ℕ, affine (q + r) ⟶ affine q
  secondProjection : ∀ q r : ℕ, affine (q + r) ⟶ affine r
  firstProjection_eq : ∀ q r : ℕ,
    (affineIso (q + r)).inv ≫ (firstProjection q r).left ≫ (affineIso q).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (Fin.castAdd r : Fin q → Fin (q + r))).toRingHom)
  secondProjection_eq : ∀ q r : ℕ,
    (affineIso (q + r)).inv ≫ (secondProjection q r).left ≫ (affineIso r).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (Fin.natAdd q : Fin r → Fin (q + r))).toRingHom)
  affineProduct : ∀ q r : ℕ, P.obj (affine q) (affine r) ≅ affine (q + r)
  affineProduct_fst : ∀ q r : ℕ, (affineProduct q r).hom ≫ firstProjection q r =
    (P.geometry (affine q) (affine r)).fst
  affineProduct_snd : ∀ q r : ℕ, (affineProduct q r).hom ≫ secondProjection q r =
    (P.geometry (affine q) (affine r)).snd
  torus : ℕ → SmoothScheme k
  torusIso : ∀ q : ℕ, (torus q).scheme.left ≅ Spec (.of (torusRing k q))
  torus_base : ∀ q : ℕ, (torus q).scheme.hom =
    (torusIso q).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (torusRing k q)))
  torusUnit : torus 0 ≅ P.unit
  torusMaps : TorusRingMaps k
  unitInsertion : ∀ (q : ℕ) (i : Fin (q + 1)), torus q ⟶ torus (q + 1)
  unitInsertion_eq : ∀ (q : ℕ) (i : Fin (q + 1)),
    (torusIso q).inv ≫ (unitInsertion q i).left ≫ (torusIso (q + 1)).hom =
      Spec.map (CommRingCat.ofHom (torusMaps.insert q i).toRingHom)
  simplexMaps : SimplexRingMaps k
  simplex : SimplexCategory ⥤ SmoothScheme k
  simplexIso : ∀ n : SimplexCategory, (simplex.obj n).scheme.left ≅ Spec (.of (simplexRing k n.len))
  simplex_base : ∀ n : SimplexCategory, (simplex.obj n).scheme.hom =
    (simplexIso n).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (simplexRing k n.len)))
  simplex_map : ∀ {m n : SimplexCategory} (a : m ⟶ n),
    (simplexIso m).inv ≫ (simplex.map a).left ≫ (simplexIso n).hom =
      Spec.map (CommRingCat.ofHom (simplexMaps.map a).toRingHom)
  simplexUnit : simplex.obj ⦋0⦌ ≅ P.unit

end MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
