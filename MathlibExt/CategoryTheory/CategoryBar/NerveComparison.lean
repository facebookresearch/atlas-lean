/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.Basic
public import MathlibExt.CategoryTheory.NerveData

/-!
# Category bar: unit-coefficient comparison with the nerve

Generic nerve simplicial `Data` (`nerveData`) and its comparison with Mathlib's
`nerve` live in `MathlibExt.CategoryTheory.NerveData`; this module provides only
the bar-specific comparison.

For unit coefficients (`ULift PUnit` on both endpoints), the degree-`n` bar
object is equivalent to `ComposableArrows C n`: both coefficient types are
subsingletons, so the chain projection is an equivalence. This promotes to a
simplicial `Data` isomorphism `barNerveUnitDataIso` between the
unit-coefficient bar data and generic `nerveData`, and further to a genuine
simplicial-set isomorphism `barNerveUnitSimplicialIso` with Mathlib's `nerve`.

References (orientation only; no exact proposition correspondence is claimed):
nLab `bar construction` (https://ncatlab.org/nlab/show/bar+construction) and
`two-sided bar construction`
(https://ncatlab.org/nlab/show/two-sided+bar+construction) pages;
Goerss–Jardine, *Simplicial Homotopy Theory*
(https://link.springer.com/book/10.1007/978-3-0348-8707-6), for
nerve/simplicial background.

Source-to-Lean map: the classical unit-coefficient two-sided bar `B(*, 𝒞, *)`
is `barObj C (unitCoeffR C) (unitCoeffL C) n`; its comparison is
`barNerveUnitSimplicialIso` against `nerve C`.

This is the arbitrary-category comparison. It is neither derived from nor a
replacement for C9's separate one-object monoid comparison
`B(*, M, *) ≅ nerve (SingleObj Mᵒᵖ)`.

Nonclaims: no comma/category-of-elements or Grothendieck comparison, and no
opposite/reversal comparison.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CategoryTheory

namespace CategoryBar

variable {C : Type u} [Category.{v} C]

/-- Constant covariant unit coefficient functor. -/
def unitCoeffL (C : Type u) [Category.{v} C] : C ⥤ Type 0 :=
  (Functor.const C).obj (ULift.{0} PUnit)

/-- Constant contravariant unit coefficient functor. -/
def unitCoeffR (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ Type 0 :=
  (Functor.const Cᵒᵖ).obj (ULift.{0} PUnit)

/-- Degreewise equivalence between the unit-coefficient bar and the nerve. -/
def barNerveUnitEquiv (C : Type u) [Category.{v} C] (n : ℕ) :
    barObj C (unitCoeffR C) (unitCoeffL C) n ≃ ComposableArrows C n where
  toFun x := x.1
  invFun F := ⟨F, ULift.up PUnit.unit, ULift.up PUnit.unit⟩
  left_inv := by
    rintro ⟨F, l, r⟩
    have hL : Subsingleton ((unitCoeffL C).obj F.left) := by
      change Subsingleton (ULift.{0} PUnit)
      infer_instance
    have hR : Subsingleton ((unitCoeffR C).obj (op F.right)) := by
      change Subsingleton (ULift.{0} PUnit)
      infer_instance
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  right_inv := by
    intro F
    rfl

@[simp]
theorem barNerveUnitEquiv_apply (n : ℕ)
    (x : barObj C (unitCoeffR C) (unitCoeffL C) n) :
    barNerveUnitEquiv C n x = barChain x :=
  rfl

@[simp]
theorem barNerveUnitEquiv_symm_apply (n : ℕ) (F : ComposableArrows C n) :
    (barNerveUnitEquiv C n).symm F =
      ⟨F, ULift.up PUnit.unit, ULift.up PUnit.unit⟩ :=
  rfl

/-- Zeroth face compatibility: the nerve `d₀` agrees with `barδ` at `0`
through the degreewise equivalence. -/
theorem barNerveUnit_face_zero {n : ℕ}
    (x : barObj C (unitCoeffR C) (unitCoeffL C) (n + 1)) :
    (nerve C).δ (0 : Fin (n + 2)) (barNerveUnitEquiv C (n + 1) x) =
      barNerveUnitEquiv C n (barδ (0 : Fin (n + 2)) x) := by
  have h := barδ_zero_eq (R := unitCoeffR C) (L := unitCoeffL C) (n := n) x
  rw [h]
  obtain ⟨F, l, r⟩ := x
  rfl

/-- Last face compatibility: the nerve `d_last` agrees with `barδ` at `last`
through the degreewise equivalence. -/
theorem barNerveUnit_face_last {n : ℕ}
    (x : barObj C (unitCoeffR C) (unitCoeffL C) (n + 1)) :
    (nerve C).δ (Fin.last (n + 1)) (barNerveUnitEquiv C (n + 1) x) =
      barNerveUnitEquiv C n (barδ (Fin.last (n + 1)) x) := by
  have h := barδ_last_eq (R := unitCoeffR C) (L := unitCoeffL C) (n := n) x
  rw [h]
  obtain ⟨F, l, r⟩ := x
  rfl

/-- Interior face compatibility: the nerve face at `q.castSucc.succ` agrees
with `barδ` through the degreewise equivalence. -/
theorem barNerveUnit_face_interior {n : ℕ} (q : Fin n)
    (x : barObj C (unitCoeffR C) (unitCoeffL C) (n + 1)) :
    (nerve C).δ (q.castSucc.succ) (barNerveUnitEquiv C (n + 1) x) =
      barNerveUnitEquiv C n (barδ (q.castSucc.succ) x) := by
  have h :=
    barδ_castSucc_succ_eq (R := unitCoeffR C) (L := unitCoeffL C) (n := n) q x
  rw [h]
  obtain ⟨F, l, r⟩ := x
  rfl

/-- Degeneracy compatibility: the nerve `s_i` agrees with `barσ` through the
degreewise equivalence, definitionally after destructuring. -/
theorem barNerveUnit_degeneracy {n : ℕ} (i : Fin (n + 1))
    (x : barObj C (unitCoeffR C) (unitCoeffL C) n) :
    (nerve C).σ i (barNerveUnitEquiv C n x) =
      barNerveUnitEquiv C (n + 1) (barσ i x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

/-- Full face compatibility for the `Data` isomorphism.

Dispatches an arbitrary `i : Fin (n + 2)` by `i.val = 0`, `i.val = n + 1`,
and the interior `q := ⟨i.val - 1, by omega⟩`. -/
theorem barNerveUnit_face_compat {n : ℕ} (i : Fin (n + 2)) :
    (Equiv.toIso (barNerveUnitEquiv C (n + 1))).hom ≫ (nerveData C).δ i =
      (categoryBarData (C := C) (R := unitCoeffR C) (L := unitCoeffL C)).δ i ≫
        (Equiv.toIso (barNerveUnitEquiv C n)).hom := by
  ext x
  change (nerve C).δ i (barNerveUnitEquiv C (n + 1) x) =
    barNerveUnitEquiv C n (barδ i x)
  by_cases h0 : i.val = 0
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    exact barNerveUnit_face_zero x
  · by_cases hL : i.val = n + 1
    · have hiL : i = Fin.last (n + 1) := by
        apply Fin.ext
        rw [hL]
        simp [Fin.val_last]
      subst hiL
      exact barNerveUnit_face_last x
    · obtain ⟨q, hk⟩ : ∃ q : Fin n, i.val = q.val + 1 :=
        ⟨⟨i.val - 1, by omega⟩, by change i.val = i.val - 1 + 1; omega⟩
      have hi : i = q.castSucc.succ := by
        apply Fin.ext
        simp [Fin.val_succ, Fin.val_castSucc, hk]
      subst hi
      exact barNerveUnit_face_interior q x

/-- Full degeneracy compatibility for the `Data` isomorphism, by function
extensionality and the pointwise lemma. -/
theorem barNerveUnit_degeneracy_compat {n : ℕ} (i : Fin (n + 1)) :
    (Equiv.toIso (barNerveUnitEquiv C n)).hom ≫ (nerveData C).σ i =
      (categoryBarData (C := C) (R := unitCoeffR C) (L := unitCoeffL C)).σ i ≫
        (Equiv.toIso (barNerveUnitEquiv C (n + 1))).hom := by
  ext x
  change (nerve C).σ i (barNerveUnitEquiv C n x) =
    barNerveUnitEquiv C (n + 1) (barσ i x)
  exact barNerveUnit_degeneracy i x

/-- Simplicial `Data` isomorphism between the unit-coefficient bar and the
nerve, assembled from the degreewise equivalence with `Data.isoOfIso`. -/
noncomputable def barNerveUnitDataIso (C : Type u) [Category.{v} C] :
    categoryBarData (C := C) (R := unitCoeffR C) (L := unitCoeffL C) ≅
      nerveData C :=
  SimplicialObject.Data.isoOfIso (fun n => Equiv.toIso (barNerveUnitEquiv C n))
    (fun i => barNerveUnit_face_compat i) (fun i => barNerveUnit_degeneracy_compat i)

/-- Genuine unit-coefficient bar comparison with Mathlib's simplicial nerve.

Composes the promoted data iso with the nerve-data comparison. -/
noncomputable def barNerveUnitSimplicialIso (C : Type u) [Category.{v} C] :
    categoryBar (C := C) (R := unitCoeffR C) (L := unitCoeffL C) ≅ nerve C :=
  (SimplicialObject.Data.toSimplicialFunctor.mapIso
    (barNerveUnitDataIso C)).trans (nerveDataSimplicialIso C)

end CategoryBar

end CategoryTheory
