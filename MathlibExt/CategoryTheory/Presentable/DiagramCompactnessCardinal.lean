/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Original small endpoint families and compatible compactness ranks

The LP rank and the supplied generation/factorization cardinal are distinct.
Both endpoints of both original arrow families are bounded from their
genuine small four-tag family. No diagram criterion or chosen factor value
is supplied as a premise.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

namespace CategoryTheory.Presentable.DiagramCompactnessCardinal

open Limits Opposite

variable (M : Type uM) [Category.{vM} M]

/-- All four endpoint tags retain the original arrow values. -/
def endpointFamily (I J : MorphismProperty M) :
    (I.toSet ⊕ J.toSet) ⊕ (I.toSet ⊕ J.toSet) → M
  | .inl (.inl i) => i.1.left
  | .inl (.inr j) => j.1.left
  | .inr (.inl i) => i.1.right
  | .inr (.inr j) => j.1.right

/-- The complete original I-source tag is unchanged. -/
theorem endpointFamily_I_source (I J : MorphismProperty M) (i : I.toSet) :
    endpointFamily M I J (.inl (.inl i)) = i.1.left := rfl

/-- The complete original J-source tag is unchanged. -/
theorem endpointFamily_J_source (I J : MorphismProperty M) (j : J.toSet) :
    endpointFamily M I J (.inl (.inr j)) = j.1.left := rfl

/-- The complete original I-target tag is unchanged. -/
theorem endpointFamily_I_target (I J : MorphismProperty M) (i : I.toSet) :
    endpointFamily M I J (.inr (.inl i)) = i.1.right := rfl

/-- The complete original J-target tag is unchanged. -/
theorem endpointFamily_J_target (I J : MorphismProperty M) (j : J.toSet) :
    endpointFamily M I J (.inr (.inr j)) = j.1.right := rfl

variable (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable M κLP]
  (S : Type w) [SmallCategory S]

/-- A genuine small original family internally supplies one uncountable regular endpoint
rank, bounding the actual index and BOTH supplied cardinal values. The original arrows
and generation/factorization cardinal κ are retained. -/
theorem endpoint_rank (κ : Cardinal.{w}) (I J : MorphismProperty M)
    [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (χ : Cardinal.{w}) (_ : Fact χ.IsRegular), κLP ≤ χ ∧ κ ≤ χ ∧
      Cardinal.aleph0 < χ ∧ HasCardinalLT (Arrow S) χ ∧
      (∀ i : I.toSet, IsCardinalPresentable i.1.left χ ∧
        IsCardinalPresentable i.1.right χ) ∧
      ∀ j : J.toSet, IsCardinalPresentable j.1.left χ ∧
        IsCardinalPresentable j.1.right χ := by
  let : IsAccessibleCategory.{w} M := ⟨κLP, inferInstance, inferInstance⟩
  let P : ObjectProperty M := ObjectProperty.ofObj (endpointFamily M I J)
  let : ObjectProperty.Small.{w} P := inferInstance
  let : ObjectProperty.EssentiallySmall.{w} P := inferInstance
  obtain ⟨μ, _, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let Upper := μ.ord.ToType ⊕ (κLP.ord.ToType ⊕
    (κ.ord.ToType ⊕ ((Cardinal.aleph0 : Cardinal.{w}).ord.ToType ⊕ Arrow S)))
  obtain ⟨χ, hRegular, hUpper⟩ := HasCardinalLT.exists_regular_cardinal Upper
  let : Fact χ.IsRegular := ⟨hRegular⟩
  have hμ : μ < χ := by
    have h := hUpper.of_injective (Sum.inl : μ.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hLP : κLP < χ := by
    have h := hUpper.of_injective
      (fun x : κLP.ord.ToType ↦ (Sum.inr (Sum.inl x) : Upper))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hκ : κ < χ := by
    have h := hUpper.of_injective
      (fun x : κ.ord.ToType ↦ (Sum.inr (Sum.inr (Sum.inl x)) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective))
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hω : Cardinal.aleph0.{w} < χ := by
    have h := hUpper.of_injective
      (fun x : (Cardinal.aleph0 : Cardinal.{w}).ord.ToType ↦
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp
        (Sum.inr_injective.comp Sum.inl_injective)))
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hArrow : HasCardinalLT (Arrow S) χ :=
    hUpper.of_injective
      (fun x : Arrow S ↦ (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp
        (Sum.inr_injective.comp Sum.inr_injective)))
  have hEndpoints (e : (I.toSet ⊕ J.toSet) ⊕ (I.toSet ⊕ J.toSet)) :
      IsCardinalPresentable (endpointFamily M I J e) χ := by
    let : IsCardinalPresentable (endpointFamily M I J e) μ :=
      hP _ (ObjectProperty.ofObj_apply (endpointFamily M I J) e)
    exact isCardinalPresentable_of_le _ hμ.le
  refine ⟨χ, inferInstance, hLP.le, hκ.le, hω, hArrow, ?_, ?_⟩
  · exact fun i ↦ ⟨hEndpoints (.inl (.inl i)), hEndpoints (.inr (.inl i))⟩
  · exact fun j ↦ ⟨hEndpoints (.inl (.inr j)), hEndpoints (.inr (.inr j))⟩

end CategoryTheory.Presentable.DiagramCompactnessCardinal
