/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.BimoduleTensorQuillen
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# The actual derived tensor of composable bimodules

The original independently ranked source generations construct both Q
factories. Their tensor is localized on the original AB, BD and AD carriers.
Both-variable weak inversion is proved by the constructed Quillen tensor
adjunctions, and ordinary computation retains both original Q counits.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wAB wBD wAD w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MorphismProperty Functor
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedBimoduleTensor

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- The original produced model determines the actual weak class on the same bimodule carrier. -/
abbrev bimoduleWeak {A B : Mon C} {I J : MorphismProperty C}
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (t : RightTransfer.OriginalRankModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A) I J κ) :
    MorphismProperty (Bimod A B) :=
  letI : ModelCategory (Bimod A B) := t.model
  weakEquivalences (Bimod A B)

variable [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {A B D : Mon C} {I J : MorphismProperty C}
  {κAB : Cardinal.{wAB}} [Fact κAB.IsRegular] [OrderBot κAB.ord.ToType]
  {κBD : Cardinal.{wBD}} [Fact κBD.IsRegular] [OrderBot κBD.ord.ToType]
  {κAD : Cardinal.{wAD}} [Fact κAD.IsRegular] [OrderBot κAD.ord.ToType]
  (tAB : RightTransfer.OriginalRankModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A) I J κAB)
  (tBD : RightTransfer.OriginalRankModelTransfer (Bimod.free B D) (Bimod.forget (B := D) B) I J κBD)
  (tAD : RightTransfer.OriginalRankModelTransfer (Bimod.free A D) (Bimod.forget (B := D) A) I J κAD)

local notation "qAB" => tAB.replacements
local notation "qBD" => tBD.replacements
local notation "WAB" => bimoduleWeak tAB
local notation "WBD" => bimoduleWeak tBD
local notation "WAD" => bimoduleWeak tAD
local notation "HAB" => MorphismProperty.Localization WAB
local notation "HBD" => MorphismProperty.Localization WBD
local notation "HAD" => MorphismProperty.Localization WAD
local notation "πAB" => MorphismProperty.Q WAB
local notation "πBD" => MorphismProperty.Q WBD
local notation "πAD" => MorphismProperty.Q WAD

/-- The original tensor is evaluated at both actual independently generated cofibrant replacements. -/
def replacedTensor : Bimod A B ⥤ Bimod B D ⥤ Bimod A D := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  exact (qAB).Q ⋙ Bimod.tensorCurried A B D ⋙
    (whiskeringLeft (Bimod B D) (Bimod B D) (Bimod A D)).obj (qBD).Q

/-- The actual tensor of both original Q objects is projected to the original AD localization. -/
def rawTensor : Bimod A B ⥤ Bimod B D ⥤ HAD :=
  replacedTensor tAB tBD ⋙ (whiskeringRight (Bimod B D) (Bimod A D) HAD).obj πAD

variable [IsCofibrant B.X]

/-- Both actual original Q maps invert every original weak pair through the proved tensor Quillen laws. -/
theorem rawTensor_inverts (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    MorphismProperty.IsInvertedBy₂ WAB WBD (rawTensor tAB tBD tAD) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := BimoduleTensorQuillen.rightTensor_weak_of_cofibrant tAB tBD tAD hI hJ
    ((qBD).Q.obj N) ((qAB).Q.map f) ((qBD).q_cofibrant N) ((qAB).q_cofibrant M)
      ((qAB).q_cofibrant M') ((qAB).q_map_weak f hf)
  have h₂ := BimoduleTensorQuillen.leftTensor_weak_of_cofibrant tAB tBD tAD hI hJ
    ((qAB).Q.obj M') ((qBD).Q.map g) ((qAB).q_cofibrant M') ((qBD).q_cofibrant N)
      ((qBD).q_cofibrant N') ((qBD).q_map_weak g hg)
  change IsIso ((πAD).map (Bimod.whiskerRight ((qAB).Q.map f) ((qBD).Q.obj N)) ≫
    (πAD).map (Bimod.whiskerLeft ((qAB).Q.obj M') ((qBD).Q.map g)))
  rw [← (πAD).map_comp]
  exact Localization.inverts πAD WAD _ ((weakEquivalences (Bimod A D)).comp_mem _ _ h₁ h₂)

/-- The actual derived tensor is a bifunctor on the three distinct original bimodule localizations. -/
def tensor (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) : HAB ⥤ HBD ⥤ HAD := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  exact Localization.lift₂ (rawTensor tAB tBD tAD) (rawTensor_inverts tAB tBD tAD hI hJ) πAB πBD

instance tensorLifting (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    Localization.Lifting₂ πAB πBD WAB WBD (rawTensor tAB tBD tAD) (tensor tAB tBD tAD hI hJ) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  unfold tensor
  infer_instance

/-- The complete two-variable source calculation is the actual natural localization projection isomorphism. -/
def projectionIso (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    (((whiskeringLeft₂ HAD).obj πAB).obj πBD).obj (tensor tAB tBD tAD hI hJ) ≅ rawTensor tAB tBD tAD :=
  Localization.Lifting₂.iso πAB πBD WAB WBD (rawTensor tAB tBD tAD) (tensor tAB tBD tAD hI hJ)

/-- Every original source pair retains the tensor of its two actual original Q objects. -/
def comparison (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    ((tensor tAB tBD tAD hI hJ).obj ((πAB).obj M)).obj ((πBD).obj N) ≅
      (πAD).obj (Bimod.tensorBimod ((qAB).Q.obj M) ((qBD).Q.obj N)) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  exact ((evaluation (Bimod B D) HAD).obj N).mapIso ((projectionIso tAB tBD tAD hI hJ).app M)

/-- Both complete original Q counits give the actual ordinary tensor comparison map. -/
def ordinaryComparisonMap (M : Bimod A B) (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    Bimod.tensorBimod ((qAB).Q.obj M) ((qBD).Q.obj N) ⟶ Bimod.tensorBimod M N := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  exact Bimod.tensorMap ((qAB).q.app M) ((qBD).q.app N)

/-- The ordinary comparison is weak at every pair of original cofibrant endpoints. -/
theorem ordinaryComparisonMap_weak (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant M → IsCofibrant N → weakEquivalences (Bimod A D) (ordinaryComparisonMap tAB tBD M N) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hM hN
  have h₁ := BimoduleTensorQuillen.rightTensor_weak_of_cofibrant tAB tBD tAD hI hJ
    ((qBD).Q.obj N) ((qAB).q.app M) ((qBD).q_cofibrant N) ((qAB).q_cofibrant M) hM
      ((qAB).q_trivialFibration M).2
  have h₂ := BimoduleTensorQuillen.leftTensor_weak_of_cofibrant tAB tBD tAD hI hJ
    M ((qBD).q.app N) hM ((qBD).q_cofibrant N) hN ((qBD).q_trivialFibration N).2
  exact (weakEquivalences (Bimod A D)).comp_mem _ _ h₁ h₂

/-- The ordinary tensor computes the actual derived tensor at all original cofibrant pairs. -/
def cofibrantComparison (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    IsCofibrant M → IsCofibrant N →
      (((tensor tAB tBD tAD hI hJ).obj ((πAB).obj M)).obj ((πBD).obj N) ≅
        (πAD).obj (Bimod.tensorBimod M N)) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  intro hM hN
  let : IsIso ((πAD).map (ordinaryComparisonMap tAB tBD M N)) :=
    Localization.inverts πAD WAD _ (ordinaryComparisonMap_weak tAB tBD tAD hI hJ M N hM hN)
  exact comparison tAB tBD tAD hI hJ M N ≪≫ asIso ((πAD).map (ordinaryComparisonMap tAB tBD M N))

end HomotopicalAlgebra.ModuleTransfer.DerivedBimoduleTensor
