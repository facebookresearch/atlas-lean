/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContraction

/-!
# Fixed-degree simplex-resolution contraction tests

These tests pin the `(x,id)` section, decoded map orientation, strict
retraction, and both endpoints of the fixed-inner replacement-row homotopy.
They make no diagonal-section or weak-equivalence claim.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContractionTests

variable {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ)

/-- The coefficient functor and its reindexing have the intended types. -/
noncomputable example : SSet.SimplexIndex Y ⥤ Type u :=
  SSet.simplexPullbackDegree p a

noncomputable example {b : SimplexCategoryᵒᵖ} (k : a ⟶ b) :
    SSet.simplexPullbackDegree p a ⟶ SSet.simplexPullbackDegree p b :=
  SSet.simplexPullbackDegreeMap p k

/-- The canonical section is represented by `p(x)` and decodes as `(x,id)`. -/
example (x : Z.obj a) :
    (SSet.simplexResolutionSigmaObj p a x).obj =
        SSet.leftFiberSimplexIndex (p.app a x) ∧
      ((SSet.simplexPullbackObjEquiv p
        (SSet.simplexResolutionSigmaObj p a x).obj a
        (SSet.simplexResolutionSigmaObj p a x).val).1).1 = x ∧
      ((SSet.simplexPullbackObjEquiv p
        (SSet.simplexResolutionSigmaObj p a x).obj a
        (SSet.simplexResolutionSigmaObj p a x).val).1).2 = 𝟙 a.unop :=
  ⟨SSet.simplexResolutionSigmaObj_obj p a x,
    SSet.simplexResolutionSigmaObj_decoded_fst p a x,
    SSet.simplexResolutionSigmaObj_decoded_snd p a x⟩

/-- Reindexing postcomposes, rather than precomposes, the decoded map. -/
example {s t : SSet.SimplexIndex Y} (_hst : s ≠ t) (u : s ⟶ t)
    (z : (pullback p s.hom).obj a) :
    ((SSet.simplexPullbackObjEquiv p t a
      ((SSet.simplexPullbackMap p u).app a z)).1).2 =
        (SSet.simplexPullbackObjEquiv p s a z).1.2 ≫ u.left :=
  SSet.simplexPullbackObjEquiv_map_snd p a u z

/-- The section followed by projection is strictly identity. -/
example :
    SSet.simplexResolutionSigma p a ⋙ SSet.simplexResolutionPi p a =
      𝟭 (Discrete (Z.obj a)) :=
  SSet.simplexResolutionSigma_comp_pi p a

/-- The contraction component uses the decoded simplex map. -/
example (e : (SSet.simplexPullbackDegree p a).Elements) :
    (SSet.simplexResolutionSigmaPiToIdApp p a e).hom.left =
      (SSet.simplexPullbackObjEquiv p e.obj a e.val).1.2 :=
  SSet.simplexResolutionSigmaPiToIdApp_left p a e

/-- The replacement-row maps have the intended types. -/
noncomputable example :
    CategoryBar.simplicialReplacement (SSet.simplexPullbackDegree p a) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  SSet.simplexResolutionDegreeAugmentation p a

/-- Degree zero projects the sole replacement coefficient to the source. -/
example (s : SSet.SimplexIndex Y)
    (x : (SSet.simplexPullbackDegree p a).obj s) :
    (SSet.simplexResolutionDegreeAugmentation p a).app (op ⦋0⦌)
        ⟨ComposableArrows.mk₀ s, x, PUnit.unit⟩ =
      (pullback.fst p s.hom).app a x :=
  SSet.simplexResolutionDegreeAugmentation_app_apply p a 0
    (ComposableArrows.mk₀ s) x PUnit.unit

/-- Degree one retains the coefficient at the source of a genuine Elements
index arrow, rather than the target coefficient. -/
example {s t : SSet.SimplexIndex Y} (u : s ⟶ t)
    (x : (SSet.simplexPullbackDegree p a).obj s) :
    (SSet.simplexResolutionDegreeAugmentation p a).app (op ⦋1⦌)
        ⟨ComposableArrows.mk₁ u, x, PUnit.unit⟩ =
      (pullback.fst p s.hom).app a x :=
  SSet.simplexResolutionDegreeAugmentation_app_apply p a 1
    (ComposableArrows.mk₁ u) x PUnit.unit

noncomputable example :
    (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) ⟶
      CategoryBar.simplicialReplacement (SSet.simplexPullbackDegree p a) :=
  SSet.simplexResolutionDegreeSection p a

/-- The fixed-inner section is a strict right inverse. -/
example :
    SSet.simplexResolutionDegreeSection p a ≫
        SSet.simplexResolutionDegreeAugmentation p a = 𝟙 _ :=
  SSet.simplexResolutionDegreeSection_comp_augmentation p a

/-- The opposite composite contracts to identity with the documented
orientation. -/
noncomputable example :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation p a ≫
        SSet.simplexResolutionDegreeSection p a)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree p a))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy p a

example :
    SSet.ι₀ ≫
        (SSet.simplexResolutionDegreeAugmentationSectionHomotopy p a).h =
      SSet.simplexResolutionDegreeAugmentation p a ≫
        SSet.simplexResolutionDegreeSection p a :=
  (SSet.simplexResolutionDegreeAugmentationSectionHomotopy p a).h₀

example :
    SSet.ι₁ ≫
        (SSet.simplexResolutionDegreeAugmentationSectionHomotopy p a).h =
      𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree p a)) :=
  (SSet.simplexResolutionDegreeAugmentationSectionHomotopy p a).h₁

section UniverseOne

variable {Z₁ Y₁ : SSet.{1}} (p₁ : Z₁ ⟶ Y₁)
  (a₁ : SimplexCategoryᵒᵖ)

noncomputable example : SSet.SimplexIndex Y₁ ⥤ Type 1 :=
  SSet.simplexPullbackDegree p₁ a₁

example :
    SSet.simplexResolutionSigma p₁ a₁ ⋙
        SSet.simplexResolutionPi p₁ a₁ =
      𝟭 (Discrete (Z₁.obj a₁)) :=
  SSet.simplexResolutionSigma_comp_pi p₁ a₁

noncomputable example :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation p₁ a₁ ≫
        SSet.simplexResolutionDegreeSection p₁ a₁)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree p₁ a₁))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy p₁ a₁

end UniverseOne

section UniverseZero

variable {Z₀ Y₀ : SSet.{0}} (p₀ : Z₀ ⟶ Y₀)
  (a₀ : SimplexCategoryᵒᵖ)

noncomputable example : SSet.SimplexIndex Y₀ ⥤ Type :=
  SSet.simplexPullbackDegree p₀ a₀

example :
    SSet.simplexResolutionSigma p₀ a₀ ⋙
        SSet.simplexResolutionPi p₀ a₀ =
      𝟭 (Discrete (Z₀.obj a₀)) :=
  SSet.simplexResolutionSigma_comp_pi p₀ a₀

noncomputable example :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation p₀ a₀ ≫
        SSet.simplexResolutionDegreeSection p₀ a₀)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree p₀ a₀))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy p₀ a₀

end UniverseZero

section BoundaryObjects

noncomputable example (a : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation
          (𝟙 (⊥_ SSet.{u})) a ≫
        SSet.simplexResolutionDegreeSection
          (𝟙 (⊥_ SSet.{u})) a)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree (𝟙 (⊥_ SSet.{u})) a))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy
    (𝟙 (⊥_ SSet.{u})) a

private abbrev twoPointConstant : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2)

noncomputable example (a : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation
          (𝟙 twoPointConstant) a ≫
        SSet.simplexResolutionDegreeSection
          (𝟙 twoPointConstant) a)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree (𝟙 twoPointConstant) a))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy
    (𝟙 twoPointConstant) a

noncomputable example (a : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation
          (𝟙 (Δ[0] : SSet.{u})) a ≫
        SSet.simplexResolutionDegreeSection
          (𝟙 (Δ[0] : SSet.{u})) a)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree (𝟙 (Δ[0] : SSet.{u})) a))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy
    (𝟙 (Δ[0] : SSet.{u})) a

noncomputable example (a : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (SSet.simplexResolutionDegreeAugmentation
          (𝟙 (Δ[1] : SSet.{u})) a ≫
        SSet.simplexResolutionDegreeSection
          (𝟙 (Δ[1] : SSet.{u})) a)
      (𝟙 (CategoryBar.simplicialReplacement
        (SSet.simplexPullbackDegree (𝟙 (Δ[1] : SSet.{u})) a))) :=
  SSet.simplexResolutionDegreeAugmentationSectionHomotopy
    (𝟙 (Δ[1] : SSet.{u})) a

end BoundaryObjects

section Privacy

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplexResolutionPiSmall

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplexResolutionSigmaSmall

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplexResolutionSmallNerveIso

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplexResolutionShrinkUnitInv

end Privacy

#check SSet.simplexResolutionPi
#check SSet.simplexResolutionSigma
#check SSet.nerveDiscreteIso

#print axioms SSet.simplexPullbackObjEquiv_map_snd
#print axioms SSet.simplexResolutionSigma_comp_pi
#print axioms SSet.simplexResolutionSigmaPiToId
#print axioms SSet.simplexResolutionDegreeAugmentation_app_apply
#print axioms SSet.simplexResolutionDegreeSection_comp_augmentation
#print axioms SSet.simplexResolutionDegreeAugmentationSectionHomotopy

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContractionTests
