/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Closed.Opposite
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorHom

/-!
# The actual right-module internal Hom of a left module

The original left module becomes a right module in the monoidal opposite.
The already constructed tensor-Hom action there is unwrapped using the
actual right-module presentation. The chosen opposite closed structure
retains every original ambient internal-Hom object and target map.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The original left action is the literal right action in the opposite tensor category. -/
def leftOpposite (N : Mod C A) : RightModuleFree.Carrier (mop A) (C := Cᴹᵒᵖ) where
  X := mop N.X
  mod :=
    { smul := N.mod.smul.mop
      one_smul := by
        exact congrArg Quiver.Hom.mop (ModObj.one_smul_self A N.X)
      mul_smul := by
        exact congrArg Quiver.Hom.mop (ModObj.mul_smul_self A N.X) }

/-- Every original left-module map keeps its literal underlying map in that presentation. -/
def leftOppositeMap {N N' : Mod C A} (f : N ⟶ N') : leftOpposite N ⟶ leftOpposite N' :=
  Mod.Hom.mk' f.hom.mop (by
    exact congrArg Quiver.Hom.mop (IsModHom.smul_hom (A := A) (f := f.hom)))

/-- The complete opposite presentation is functorial on all original left modules. -/
def leftOppositeFunctor (A : C) [MonObj A] : Mod C A ⥤ RightModuleFree.Carrier (mop A) (C := Cᴹᵒᵖ) where
  obj := leftOpposite
  map := leftOppositeMap
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

variable [BraidedCategory C] [MonoidalClosed C]

/-- The original closed structure transported to the monoidal opposite for the right-module Hom. -/
local instance oppositeClosed : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)

/-- The actual right-module Hom functor, using the original opposite tensor-Hom action and wrapper. -/
def rightHomFunctor (N : Mod C A) : C ⥤ RightModuleFree.Carrier A :=
  mopFunctor C ⋙ homFunctor (leftOpposite N) ⋙ RightModuleFree.unmopModules A

/-- The entire right-module Hom object has the original ambient internal-Hom carrier. -/
theorem rightHomFunctor_obj (N : Mod C A) (X : C) :
    ((rightHomFunctor N).obj X).X = (ihom N.X).obj X := rfl

/-- Every original target map is its same complete ambient internal-Hom map. -/
theorem rightHomFunctor_map_hom (N : Mod C A) {X Y : C} (f : X ⟶ Y) :
    ((rightHomFunctor N).map f).hom = (ihom N.X).map f := rfl

/-- The full right scalar action is the original source action followed by the actual right evaluation. -/
theorem rightHomFunctor_smul (N : Mod C A) (X : C) :
    ((rightHomFunctor N).obj X).mod.smul =
      (originalRightTensorAdjunction N.X).homEquiv (((ihom N.X).obj X) ⊗ A) X
        ((α_ ((ihom N.X).obj X) A N.X).hom ≫
          ((ihom N.X).obj X ◁ N.mod.smul) ≫
            (originalRightTensorAdjunction N.X).counit.app X) := by
  let H := (ihom N.X).obj X
  let pair := homActionPairing (leftOpposite N) (mop X)
  have hp : pair.unmop = (α_ H A N.X).hom ≫ (H ◁ N.mod.smul) ≫
      (originalRightTensorAdjunction N.X).counit.app X := by
    change ((α_ H A N.X).hom ≫ (H ◁ N.mod.smul)) ≫
      ((ihom.ev (mop N.X)).app (mop X)).unmop = _
    rw [Category.assoc, monoidalClosedOpposite_counit]
  have h := monoidalClosedOpposite_homEquiv N.X (H ⊗ A) X pair.unmop
  change ((rightHomFunctor N).obj X).mod.smul =
    (originalRightTensorAdjunction N.X).homEquiv (H ⊗ A) X pair.unmop at h
  rw [hp] at h
  exact h

section Tensor

variable [Limits.HasColimitsOfSize.{0, 0} C]

open CategoryTheory.Limits

local instance unmopEquivalence : (unmopFunctor C).IsEquivalence :=
  (unmopEquiv C).isEquivalence_functor

local instance oppositeColimits : HasColimitsOfSize.{0, 0} Cᴹᵒᵖ := by
  let : CreatesColimitsOfSize.{0, 0} (unmopFunctor C) :=
    Functor.createsColimitsOfIsEquivalence (unmopFunctor C)
  exact hasColimits_of_hasColimits_createsColimits (unmopFunctor C)

/-- The complete chosen coequalizer is unchanged when its two original balancing arrows are exchanged. -/
def swappedCoequalizerIso {X Y : C} (f g : X ⟶ Y) :
    coequalizer f g ≅ coequalizer g f where
  hom := coequalizer.desc (coequalizer.π g f) (coequalizer.condition g f).symm
  inv := coequalizer.desc (coequalizer.π f g) (coequalizer.condition f g).symm
  hom_inv_id := by
    apply coequalizer.hom_ext
    rw [← Category.assoc, coequalizer.π_desc, coequalizer.π_desc, Category.comp_id]
  inv_hom_id := by
    apply coequalizer.hom_ext
    rw [← Category.assoc, coequalizer.π_desc, coequalizer.π_desc, Category.comp_id]

/-- Unwrapping the actual opposite tensor gives the two original balancing maps in reverse order. -/
def oppositeTensorCoequalizerIso (M : RightModuleFree.Carrier A) (N : Mod C A) :
    unmop (tensorObject (leftOpposite N) (RightModuleFree.mopModule A M)) ≅
      coequalizer ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) (rightAction M ▷ N.X) :=
  (unmopFunctor C).mapIso
      (tensorCoequalizerIso (leftOpposite N) (RightModuleFree.mopModule A M)) ≪≫
    (PreservesCoequalizer.iso (unmopFunctor C)
      (pointFst (leftOpposite N) (RightModuleFree.mopModule A M))
      (pointSnd (leftOpposite N) (RightModuleFree.mopModule A M))).symm

/-- The original source associator identifies the complete ordinary balancing diagrams. -/
def tensorSourceBalancingDiagramIso (M : RightModuleFree.Carrier A) (N : Mod C A) :
    parallelPair (pointFst M N) (pointSnd M N) ≅
      parallelPair (rightAction M ▷ N.X) ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) :=
    parallelPairIso (pointFst M N) (pointSnd M N) (rightAction M ▷ N.X)
      ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul)
      (α_ M.X A N.X).symm (Iso.refl (M.X ⊗ N.X))
      (by
        change ((α_ M.X A N.X).inv ≫ rightAction M ▷ N.X) ≫ 𝟙 _ =
          (α_ M.X A N.X).inv ≫ rightAction M ▷ N.X
        exact Category.comp_id _)
      (by
        change (M.X ◁ N.mod.smul) ≫ 𝟙 _ =
          (α_ M.X A N.X).inv ≫ (α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul
        rw [Category.comp_id, Iso.inv_hom_id_assoc])

/-- The same source associator identifies the two complete chosen balancing coequalizers. -/
def tensorSourceCoequalizerIso (M : RightModuleFree.Carrier A) (N : Mod C A) :
    tensorObject M N ≅
      coequalizer (rightAction M ▷ N.X) ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) :=
  tensorCoequalizerIso M N ≪≫ HasColimit.isoOfNatIso (tensorSourceBalancingDiagramIso M N)

/-- The original balanced tensor is the exact unwrapped opposite tensor, including its chosen coequalizer. -/
def oppositeTensorIso (M : RightModuleFree.Carrier A) (N : Mod C A) :
    tensorObject M N ≅ unmop (tensorObject (leftOpposite N) (RightModuleFree.mopModule A M)) :=
  tensorSourceCoequalizerIso M N ≪≫
    (oppositeTensorCoequalizerIso M N ≪≫
      swappedCoequalizerIso ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) (rightAction M ▷ N.X)).symm

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The normalized source coequalizer keeps its original entire quotient projection. -/
theorem tensorSourceCoequalizerIso_projection (M : RightModuleFree.Carrier A) (N : Mod C A) :
    projection M N ≫ (tensorSourceCoequalizerIso M N).hom =
      coequalizer.π (rightAction M ▷ N.X) ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) := by
  unfold tensorSourceCoequalizerIso
  rw [Iso.trans_hom, ← Category.assoc, projection_coequalizer]
  have h := HasColimit.ι_isoOfNatIso_hom (tensorSourceBalancingDiagramIso M N) WalkingParallelPair.one
  change coequalizer.π (pointFst M N) (pointSnd M N) ≫
      (HasColimit.isoOfNatIso (tensorSourceBalancingDiagramIso M N)).hom =
    𝟙 (M.X ⊗ N.X) ≫
      coequalizer.π (rightAction M ▷ N.X) ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) at h
  rw [Category.id_comp] at h
  exact h

omit [BraidedCategory C] [MonoidalClosed C] in
/-- Unwrapping the opposite quotient keeps the same original projection before swapping its pair. -/
theorem oppositeTensorCoequalizerIso_projection (M : RightModuleFree.Carrier A) (N : Mod C A) :
    (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M)) ≫
        (oppositeTensorCoequalizerIso M N).hom =
      coequalizer.π ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) (rightAction M ▷ N.X) := by
  unfold oppositeTensorCoequalizerIso
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, projection_coequalizer]
  exact map_π_preserves_coequalizer_inv _ _ _

omit [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] in
/-- Exchanging the original balancing pair retains the same quotient leg. -/
theorem swappedCoequalizerIso_projection {X Y : C} (f g : X ⟶ Y) :
    coequalizer.π f g ≫ (swappedCoequalizerIso f g).hom = coequalizer.π g f := by
  exact coequalizer.π_desc _ _

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The full opposite tensor comparison keeps the actual original quotient projection. -/
theorem oppositeTensorIso_projection (M : RightModuleFree.Carrier A) (N : Mod C A) :
    projection M N ≫ (oppositeTensorIso M N).hom =
      (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M)) := by
  let e := oppositeTensorCoequalizerIso M N ≪≫
    swappedCoequalizerIso ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul) (rightAction M ▷ N.X)
  apply (cancel_mono e.hom).mp
  change (projection M N ≫ ((tensorSourceCoequalizerIso M N).hom ≫ e.inv)) ≫ e.hom = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    tensorSourceCoequalizerIso_projection]
  change _ = (unmopFunctor C).map
    (projection (leftOpposite N) (RightModuleFree.mopModule A M)) ≫
      ((oppositeTensorCoequalizerIso M N).hom ≫
        (swappedCoequalizerIso ((α_ M.X A N.X).hom ≫ M.X ◁ N.mod.smul)
          (rightAction M ▷ N.X)).hom)
  rw [← Category.assoc, oppositeTensorCoequalizerIso_projection, swappedCoequalizerIso_projection]

/-- The exact opposite tensor comparison is natural in every original right-module map. -/
def oppositeTensorNatIso (N : Mod C A) : rightTensorFunctor N ≅
    RightModuleFree.mopModules A ⋙ leftTensorFunctor (leftOpposite N) ⋙ unmopFunctor C :=
  NatIso.ofComponents (fun M => oppositeTensorIso M N) (by
    intro M M' f
    apply tensor_hom_ext M N
    rw [← Category.assoc, rightTensorFunctor_projection, Category.assoc, oppositeTensorIso_projection,
      ← Category.assoc, oppositeTensorIso_projection]
    have h := congrArg Quiver.Hom.unmop
      (tensorMap_projection (𝟙 (leftOpposite N)) ((RightModuleFree.mopModules A).map f))
    have hs := h.symm
    simp only [Mod.id_hom', tensorHom_def, id_whiskerRight, Category.id_comp] at hs
    change (f.hom ▷ N.X) ≫
        (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M')) =
      (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M)) ≫
        (unmopFunctor C).map
          (tensorMap (𝟙 (leftOpposite N)) ((RightModuleFree.mopModules A).map f))
    change (f.hom ▷ N.X) ≫
        (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M')) =
      (unmopFunctor C).map (projection (leftOpposite N) (RightModuleFree.mopModule A M)) ≫
        (unmopFunctor C).map
          (tensorMap (𝟙 (leftOpposite N)) ((RightModuleFree.mopModules A).map f)) at hs
    exact hs)

/-- The original balanced right tensor has the actual right-module Hom as its right adjoint. -/
def rightTensorHomAdjunction (N : Mod C A) : rightTensorFunctor N ⊣ rightHomFunctor N :=
  (((RightModuleFree.moduleEquivalence A).symm.toAdjunction.comp
      (tensorHomAdjunction (leftOpposite N))).comp (unmopEquiv C).toAdjunction).ofNatIsoLeft
    (oppositeTensorNatIso N).symm

end Tensor

end CategoryTheory.Mod.RightLeftTensor
