/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSmashFlatness.Base

/-!
# The actual auxiliary-model pretty-small source condition

Pretty smallness supplies an actual auxiliary cofibrantly generated model on
the same base category, with the same weak class, smaller cofibrations, and
compact domains and codomains of its actual generating cofibrations. The
resulting base couniversal weak cell closure is proved from those sources.
No spectrum model or tensor weak-preservation outcome is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.PositiveLevelModel

variable (C : Type u) [Category.{v} C] [baseModel : ModelCategory C]

local instance prettyAleph0Regular : Fact (Cardinal.aleph0.{w}).IsRegular := Cardinal.fact_isRegular_aleph0

/-- The exact original auxiliary-model definition of pretty smallness. -/
structure PrettySmallSource where
  /-- The actual auxiliary model on the same original base category. -/
  auxiliary : ModelCategory C
  weak_eq : auxiliary.categoryWithWeakEquivalences.weakEquivalences =
      baseModel.categoryWithWeakEquivalences.weakEquivalences
  cofibrations_le : auxiliary.categoryWithCofibrations.cofibrations ≤ baseModel.categoryWithCofibrations.cofibrations
  /-- The original generating cofibrations of the auxiliary model. -/
  I : MorphismProperty C
  /-- The original generating trivial cofibrations of the auxiliary model. -/
  J : MorphismProperty C
  I_smallObject : I.HasSmallObjectArgument.{w}
  J_smallObject : J.HasSmallObjectArgument.{w}
  I_rlp : I.rlp = auxiliary.categoryWithFibrations.fibrations ⊓ auxiliary.categoryWithWeakEquivalences.weakEquivalences
  J_rlp : J.rlp = auxiliary.categoryWithFibrations.fibrations
  domains_compact (i : I.toSet) : IsCardinalPresentable i.1.left (Cardinal.aleph0.{w})
  codomains_compact (i : I.toSet) : IsCardinalPresentable i.1.right (Cardinal.aleph0.{w})

variable {C}

/-- Compact original endpoints are genuinely compact relative to every actual base transition arrow. -/
theorem PrettySmallSource.compactTop (h : PrettySmallSource.{w} C) : CompactGeneratingSources.{w} h.I ⊤ := by
  constructor
  · intro i K _ _ F _
    let _ : IsCardinalPresentable i.1.left (Cardinal.aleph0.{w}) := h.domains_compact i
    let _ : IsCardinalFiltered K (Cardinal.aleph0.{w}) :=
      (isCardinalFiltered_aleph0_iff K).mpr inferInstance
    let _ : PreservesColimitsOfShape K (coyoneda.obj (op i.1.left)) :=
      preservesColimitsOfShape_of_isCardinalPresentable i.1.left (Cardinal.aleph0.{w}) K
    infer_instance
  · intro i K _ _ F _
    let _ : IsCardinalPresentable i.1.right (Cardinal.aleph0.{w}) := h.codomains_compact i
    let _ : IsCardinalFiltered K (Cardinal.aleph0.{w}) :=
      (isCardinalFiltered_aleph0_iff K).mpr inferInstance
    let _ : PreservesColimitsOfShape K (coyoneda.obj (op i.1.right)) :=
      preservesColimitsOfShape_of_isCardinalPresentable i.1.right (Cardinal.aleph0.{w}) K
    infer_instance

variable [MonoidalCategory C]

/-- Genuine h-monoidality and the source cofibration inclusion make the actual auxiliary model left proper. -/
theorem PrettySmallSource.auxiliary_isLeftProper (h : PrettySmallSource.{w} C) (hm : HMonoidality C) :
    let _ : ModelCategory C := h.auxiliary
    IsLeftProper C := by
  change @IsLeftProper C _ h.auxiliary.categoryWithWeakEquivalences h.auxiliary.categoryWithCofibrations
  refine @IsLeftProper.mk C _ h.auxiliary.categoryWithWeakEquivalences h.auxiliary.categoryWithCofibrations ?_
  refine { isStableUnderCobaseChangeAlong := ?_ }
  intro A B f hf
  have hOld := hm.cofibrations_le_hCofibrations f (h.cofibrations_le f hf)
  have hs := hOld A B (𝟙 A) f (𝟙 B) IsPushout.of_id_fst
  change h.auxiliary.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAlong f
  rw [h.weak_eq]
  exact hs

variable [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

omit [MonoidalCategory C] in
/-- Pretty smallness earns full couniversal weak transfinite closure from the actual compact auxiliary generators. -/
theorem PrettySmallSource.couniversal_transfinite (h : PrettySmallSource.{w} C) :
    (couniversalWeakEquivalences C).IsStableUnderTransfiniteComposition.{w} := by
  let originalI : MorphismProperty C := h.I
  have hCompact : CompactGeneratingSources.{w} originalI ⊤ := h.compactTop
  have hActualI : originalI.rlp = h.auxiliary.categoryWithFibrations.fibrations ⊓
      h.auxiliary.categoryWithWeakEquivalences.weakEquivalences := h.I_rlp
  have hTop : (⊤ : MorphismProperty C).IsStableUnderTransfiniteComposition.{w} :=
    { isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ := { le := le_top } }
  have hCobase : (⊤ : MorphismProperty C).IsStableUnderCobaseChange := inferInstance
  have haux : (@couniversalWeakEquivalences C _ h.auxiliary.categoryWithWeakEquivalences ⊓
      (⊤ : MorphismProperty C)).IsStableUnderTransfiniteComposition.{w} :=
    @couniversalIntersection_isStableUnderTransfiniteComposition_of_compact.{w}
      C _ h.auxiliary inferInstance inferInstance originalI ⊤ hActualI hCompact le_top hTop hCobase
  have he : @couniversalWeakEquivalences C _ h.auxiliary.categoryWithWeakEquivalences =
      @couniversalWeakEquivalences C _ baseModel.categoryWithWeakEquivalences := by
    unfold couniversalWeakEquivalences
    change (fun A B (f : A ⟶ B) => ∀ (X Y : C) (a : A ⟶ X) (q : X ⟶ Y) (b : B ⟶ Y),
      IsPushout a f q b → h.auxiliary.categoryWithWeakEquivalences.weakEquivalences q) =
      (fun A B (f : A ⟶ B) => ∀ (X Y : C) (a : A ⟶ X) (q : X ⟶ Y) (b : B ⟶ Y),
        IsPushout a f q b → baseModel.categoryWithWeakEquivalences.weakEquivalences q)
    rw [h.weak_eq]
  simpa only [inf_top_eq, he] using haux

end HomotopicalAlgebra.PositiveLevelModel
