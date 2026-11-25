/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.SequentialProjectiveCofibrant

/-!
# The actual projective colimit Quillen adjunction

The existing colimit–constant adjunction is Quillen when the prescribed
diagram right classes are the original objectwise classes. Brown's
lemma then applies to genuinely cofibrant diagrams. For sequences,
their initial objects and original transition cofibrations supply that
cofibrancy through the compatible lifting construction.
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.ProjectiveColimit

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {J : Type w} [Category.{z} J] [HasColimitsOfShape J C] [ModelCategory (J ⥤ C)]

/-- The native colimit–constant adjunction is Quillen for the specified original objectwise right
classes. -/
theorem isQuillenAdjunction
    (hF : fibrations (J ⥤ C) = (fibrations C).functorCategory J)
    (hT : trivialFibrations (J ⥤ C) = (trivialFibrations C).functorCategory J) :
    (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [hF]
    intro j
    exact hf
  · intro X Y f hf
    rw [hT]
    intro j
    exact hf

/-- Pointwise weak maps of cofibrant projective diagrams induce the actual weak colimit map. -/
theorem weakEquivalence_colimMap
    (hF : fibrations (J ⥤ C) = (fibrations C).functorCategory J)
    (hT : trivialFibrations (J ⥤ C) = (trivialFibrations C).functorCategory J)
    (hW : weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J)
    {F G : J ⥤ C} (α : F ⟶ G) [IsCofibrant F] [IsCofibrant G]
    (hα : ∀ j, weakEquivalences C (α.app j)) : WeakEquivalence (colimMap α) := by
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction :=
    isQuillenAdjunction hF hT
  let _ : WeakEquivalence α := (weakEquivalence_iff _).mpr (by rw [hW]; exact hα)
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := colimConstAdj) α

/-- The whole map of supplied genuine colimit cocones is weak, retaining every original cocone leg.
-/
theorem weakEquivalence_of_isColimits
    (hF : fibrations (J ⥤ C) = (fibrations C).functorCategory J)
    (hT : trivialFibrations (J ⥤ C) = (trivialFibrations C).functorCategory J)
    (hW : weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J)
    {F G : J ⥤ C} (α : F ⟶ G) [IsCofibrant F] [IsCofibrant G]
    (hα : ∀ j, weakEquivalences C (α.app j))
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j, cF.ι.app j ≫ d = α.app j ≫ cG.ι.app j) :
    WeakEquivalence d := by
  let eF := (colimit.isColimit F).coconePointUniqueUpToIso hcF
  let eG := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  have commutation : eF.hom ≫ d = colimMap α ≫ eG.hom := by
    apply colimit.hom_ext
    intro j
    have hf : colimit.ι F j ≫ eF.hom = cF.ι.app j :=
      colimit.comp_coconePointUniqueUpToIso_hom hcF j
    have hg : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
      colimit.comp_coconePointUniqueUpToIso_hom hcG j
    calc
      colimit.ι F j ≫ eF.hom ≫ d = cF.ι.app j ≫ d := by rw [← Category.assoc, hf]
      _ = α.app j ≫ cG.ι.app j := hd j
      _ = α.app j ≫ colimit.ι G j ≫ eG.hom := by rw [hg]
      _ = colimit.ι F j ≫ colimMap α ≫ eG.hom := by rw [ι_colimMap_assoc]
  let _ : WeakEquivalence (colimMap α) := weakEquivalence_colimMap hF hT hW α hα
  have hcolim : weakEquivalences C (colimMap α) := mem_weakEquivalences _
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences C).arrow_mk_iso_iff (Arrow.isoMk eF eG commutation)).mp hcolim)

section Sequences

variable [HasColimitsOfShape ℕ C] [ModelCategory (ℕ ⥤ C)]

/-- Cofibrant initial objects and the original transition cofibrations suffice for weak preservation
on the entire sequential colimit map. -/
theorem weakEquivalence_of_sequence_isColimits
    (hF : fibrations (ℕ ⥤ C) = (fibrations C).functorCategory ℕ)
    (hT : trivialFibrations (ℕ ⥤ C) = (trivialFibrations C).functorCategory ℕ)
    (hW : weakEquivalences (ℕ ⥤ C) = (weakEquivalences C).functorCategory ℕ)
    {F G : ℕ ⥤ C} (α : F ⟶ G) [IsCofibrant (F.obj 0)] [IsCofibrant (G.obj 0)]
    (hstepF : ∀ n : ℕ, Cofibration (F.map (homOfLE (n.le_add_right 1))))
    (hstepG : ∀ n : ℕ, Cofibration (G.map (homOfLE (n.le_add_right 1))))
    (hα : ∀ n, weakEquivalences C (α.app n))
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ n, cF.ι.app n ≫ d = α.app n ≫ cG.ι.app n) :
    WeakEquivalence d := by
  let _ : IsCofibrant F :=
    SequentialProjectiveLifting.isCofibrant_of_cofibration_transitions hT F hstepF
  let _ : IsCofibrant G :=
    SequentialProjectiveLifting.isCofibrant_of_cofibration_transitions hT G hstepG
  exact weakEquivalence_of_isColimits hF hT hW α hα hcF hcG d hd

end Sequences

end HomotopicalAlgebra.ProjectiveColimit
