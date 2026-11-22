/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorFunctor
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorFree

/-!
# Bimodule composition and the original right-left balanced tensor

The two balancing diagrams differ by their original source associator.
Their chosen coequalizers are therefore naturally isomorphic, with the
same quotient projections and every original module map. The existing
free-left split coequalizer gives the actual one-sided free reduction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open CategoryTheory.Mod
open scoped MonoidalCategory

namespace Bimod

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B D : Mon C}


/-- The original two balancing pairs retain both actions and differ only by the source associator. -/
def tensorBalancingDiagramIso (M : Bimod A B) (N : Bimod B D) :
    parallelPair (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft) ≅
      parallelPair (RightLeftTensor.pointFst (toRightModule M) (toLeftModule N))
        (RightLeftTensor.pointSnd (toRightModule M) (toLeftModule N)) :=
  parallelPairIso _ _ _ _ (α_ M.X B.X N.X) (Iso.refl (M.X ⊗ N.X))
    (by
      change (M.actRight ▷ N.X) ≫ 𝟙 _ =
        (α_ M.X B.X N.X).hom ≫ (α_ M.X B.X N.X).inv ≫ (M.actRight ▷ N.X)
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
    (by
      change ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft) ≫ 𝟙 _ =
        (α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft
      exact Category.comp_id _)

/-- The original bimodule coequalizer is the actual balanced tensor of its two one-sided modules. -/
def tensorUnderlyingIso (M : Bimod A B) (N : Bimod B D) :
    (tensorBimod M N).X ≅ RightLeftTensor.tensorObject (toRightModule M) (toLeftModule N) :=
  HasColimit.isoOfNatIso (tensorBalancingDiagramIso M N) ≪≫
    (RightLeftTensor.tensorCoequalizerIso (toRightModule M) (toLeftModule N)).symm

/-- The full original quotient projection is retained by the one-sided tensor comparison. -/
theorem tensorUnderlyingIso_projection (M : Bimod A B) (N : Bimod B D) :
    tensorProjection M N ≫ (tensorUnderlyingIso M N).hom =
      RightLeftTensor.projection (toRightModule M) (toLeftModule N) := by
  have h := HasColimit.ι_isoOfNatIso_hom (tensorBalancingDiagramIso M N) WalkingParallelPair.one
  change tensorProjection M N ≫ (HasColimit.isoOfNatIso (tensorBalancingDiagramIso M N)).hom =
    𝟙 (M.X ⊗ N.X) ≫ coequalizer.π (RightLeftTensor.pointFst (toRightModule M) (toLeftModule N))
      (RightLeftTensor.pointSnd (toRightModule M) (toLeftModule N)) at h
  rw [Category.id_comp] at h
  change tensorProjection M N ≫
    ((HasColimit.isoOfNatIso (tensorBalancingDiagramIso M N)).hom ≫
      (RightLeftTensor.tensorCoequalizerIso (toRightModule M) (toLeftModule N)).inv) = _
  rw [← Category.assoc, h, ← RightLeftTensor.projection_from_coequalizer]

/-- The same original tensor projection is epimorphic. -/
instance tensorProjection_epi (M : Bimod A B) (N : Bimod B D) : Epi (tensorProjection M N) := by
  unfold tensorProjection
  infer_instance

/-- Every original bimodule map commutes with the same one-sided balanced tensor comparison. -/
theorem tensorUnderlyingIso_naturality {M M' : Bimod A B} {N N' : Bimod B D}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensorMap f g).hom ≫ (tensorUnderlyingIso M' N').hom =
      (tensorUnderlyingIso M N).hom ≫
        RightLeftTensor.tensorMap ((rightModuleFunctor A B).map f) ((leftModuleFunctor B D).map g) := by
  apply (cancel_epi (tensorProjection M N)).mp
  rw [← Category.assoc, tensorMap_projection, Category.assoc, tensorUnderlyingIso_projection,
    ← Category.assoc, tensorUnderlyingIso_projection, RightLeftTensor.tensorMap_projection]
  rfl

/-- Tensoring with the actual free right-hand bimodule reduces through the original free-left split pair. -/
def tensorFreeUnderlyingIso (M : Bimod A B) (Y : C) :
    (tensorBimod M (freeObject B D Y)).X ≅ M.X ⊗ (Y ⊗ D.X) :=
  tensorUnderlyingIso M (freeObject B D Y) ≪≫
    (RightLeftTensor.leftTensorFunctor (toRightModule M)).mapIso (freeLeftModuleIso B D Y) ≪≫
      RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)

/-- The free reduction is the original associator and right action after the exact quotient map. -/
theorem tensorFreeUnderlyingIso_projection (M : Bimod A B) (Y : C) :
    tensorProjection M (freeObject B D Y) ≫ (tensorFreeUnderlyingIso M Y).hom =
      (M.X ◁ (α_ B.X Y D.X).hom) ≫ (α_ M.X B.X (Y ⊗ D.X)).inv ≫
        (M.actRight ▷ (Y ⊗ D.X)) := by
  change tensorProjection M (freeObject B D Y) ≫
    ((tensorUnderlyingIso M (freeObject B D Y)).hom ≫
      ((RightLeftTensor.leftTensorFunctor (toRightModule M)).map (freeLeftModuleIso B D Y).hom ≫
        (RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)).hom)) = _
  have h₁ := tensorUnderlyingIso_projection M (freeObject B D Y)
  have h₂ := RightLeftTensor.leftTensorFunctor_projection
    (toRightModule M) (freeLeftModuleIso B D Y).hom
  have h₃ := RightLeftTensor.freeTensorIso_projection (toRightModule M) (Y ⊗ D.X)
  calc
    _ = RightLeftTensor.projection (toRightModule M) (toLeftModule (freeObject B D Y)) ≫
        ((RightLeftTensor.leftTensorFunctor (toRightModule M)).map (freeLeftModuleIso B D Y).hom ≫
          (RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ ((RightLeftTensor.leftTensorFunctor (toRightModule M)).map
          (freeLeftModuleIso B D Y).hom ≫
            (RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)).hom)) h₁
    _ = ((toRightModule M).X ◁ (freeLeftModuleIso B D Y).hom.hom) ≫
        RightLeftTensor.projection (toRightModule M) ((Mod.free B.X).obj (Y ⊗ D.X)) ≫
          (RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (RightLeftTensor.freeTensorIso (toRightModule M) (Y ⊗ D.X)).hom) h₂
    _ = _ := by
      rw [h₃, freeLeftModuleIso_hom]
      rfl

end Bimod
