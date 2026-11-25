/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.Opposite
public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorUniversal
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightTensorHom

/-!
# The actual tensor comparison in the opposite bimodule presentation

The original source associator and pair exchange identify the two balancing
coequalizers. Their entire projections are retained. The comparison preserves
both actual outer actions and is natural in both original bimodule maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

/-- The chosen closed structure on the monoidal opposite used in the bimodule tensor comparison. -/
local instance oppositeTensorClosed : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
local instance oppositeTensorUnwrapEquivalence :
    (CategoryTheory.unmopFunctor C).IsEquivalence :=
  (CategoryTheory.MonoidalOpposite.unmopEquiv C).isEquivalence_functor

local instance oppositeTensorColimits : HasColimitsOfSize.{0, 0} Cᴹᵒᵖ := by
  let : CreatesColimitsOfSize.{0, 0} (CategoryTheory.unmopFunctor C) :=
    Functor.createsColimitsOfIsEquivalence _
  exact hasColimits_of_hasColimits_createsColimits (CategoryTheory.unmopFunctor C)

local instance oppositeTensorLeftPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) := (ihom.adjunction X).leftAdjoint_preservesColimits
local instance oppositeTensorRightPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  (originalRightTensorAdjunction X).leftAdjoint_preservesColimits

/-- The original source associator identifies the complete balancing pair with the swapped opposite pair. -/
def mopTensorBalancingIso (M : Bimod A B) (N : Bimod B D) :
    parallelPair (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft) ≅
      parallelPair ((α_ M.X B.X N.X).inv ≫ (M.actRight ▷ N.X)) (M.X ◁ N.actLeft) :=
  parallelPairIso _ _ _ _ (α_ M.X B.X N.X) (Iso.refl (M.X ⊗ N.X))
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
    (by simp only [Iso.refl_hom, Category.comp_id])

/-- The complete original tensor quotient is the unwrapped opposite tensor quotient. -/
def mopTensorUnderlyingIso (M : Bimod A B) (N : Bimod B D) :
    (tensorBimod M N).X ≅ unmop (tensorBimod (mopBimodule N) (mopBimodule M)).X :=
  HasColimit.isoOfNatIso (mopTensorBalancingIso M N) ≪≫
    Mod.RightLeftTensor.swappedCoequalizerIso ((α_ M.X B.X N.X).inv ≫ (M.actRight ▷ N.X))
      (M.X ◁ N.actLeft) ≪≫
        PreservesCoequalizer.iso (CategoryTheory.unmopFunctor C)
          ((mopBimodule N).actRight ▷ (mopBimodule M).X)
          ((α_ (mopBimodule N).X (mopMon B).X (mopBimodule M).X).hom ≫
            (mopBimodule N).X ◁ (mopBimodule M).actLeft)

/-- The complete tensor comparison retains the literal original quotient projection. -/
@[reassoc] theorem mopTensorUnderlyingIso_projection (M : Bimod A B) (N : Bimod B D) :
    tensorProjection M N ≫ (mopTensorUnderlyingIso M N).hom =
      (CategoryTheory.unmopFunctor C).map
        (tensorProjection (mopBimodule N) (mopBimodule M)) := by
  let f := (α_ M.X B.X N.X).inv ≫ (M.actRight ▷ N.X)
  let g := M.X ◁ N.actLeft
  have h := HasColimit.ι_isoOfNatIso_hom (mopTensorBalancingIso M N) WalkingParallelPair.one
  change tensorProjection M N ≫ (HasColimit.isoOfNatIso (mopTensorBalancingIso M N)).hom =
    𝟙 (M.X ⊗ N.X) ≫ coequalizer.π f g at h
  rw [Category.id_comp] at h
  rw [mopTensorUnderlyingIso, Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← Category.assoc, h]
  rw [Mod.RightLeftTensor.swappedCoequalizerIso_projection]
  let F := CategoryTheory.unmopFunctor C
  let a := (mopBimodule N).actRight ▷ (mopBimodule M).X
  let b := (α_ (mopBimodule N).X (mopMon B).X (mopBimodule M).X).hom ≫
    (mopBimodule N).X ◁ (mopBimodule M).actLeft
  change coequalizer.π (F.map a) (F.map b) ≫ (PreservesCoequalizer.iso F a b).hom =
    F.map (coequalizer.π a b)
  have hp := map_π_preserves_coequalizer_inv F a b
  rw [← hp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The complete original right action is the opposite tensor's left action under the comparison. -/
theorem mopTensorUnderlyingIso_rightAction (M : Bimod A B) (N : Bimod B D) :
    (tensorBimod M N).actRight ≫ (mopTensorUnderlyingIso M N).hom =
      ((mopTensorUnderlyingIso M N).hom ▷ D.X) ≫
        (tensorBimod (mopBimodule N) (mopBimodule M)).actLeft.unmop := by
  refine (cancel_epi ((tensorRight D.X).map
    (coequalizer.π (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft)))).mp ?_
  change (tensorProjection M N ▷ D.X) ≫ (tensorBimod M N).actRight ≫ (mopTensorUnderlyingIso M N).hom =
    (tensorProjection M N ▷ D.X) ≫ ((mopTensorUnderlyingIso M N).hom ▷ D.X) ≫
      (tensorBimod (mopBimodule N) (mopBimodule M)).actLeft.unmop
  rw [tensorProjection_rightAction_assoc, mopTensorUnderlyingIso_projection,
    ← comp_whiskerRight_assoc, mopTensorUnderlyingIso_projection]
  have h := congrArg Quiver.Hom.unmop (tensorProjection_leftAction (mopBimodule N) (mopBimodule M))
  change ((CategoryTheory.unmopFunctor C).map
      (tensorProjection (mopBimodule N) (mopBimodule M)) ▷ D.X) ≫
      (tensorBimod (mopBimodule N) (mopBimodule M)).actLeft.unmop =
    (α_ M.X N.X D.X).hom ≫ (M.X ◁ N.actRight) ≫
      (CategoryTheory.unmopFunctor C).map
        (tensorProjection (mopBimodule N) (mopBimodule M)) at h
  exact h.symm

/-- The complete original left action is the opposite tensor's right action under the comparison. -/
theorem mopTensorUnderlyingIso_leftAction (M : Bimod A B) (N : Bimod B D) :
    (tensorBimod M N).actLeft ≫ (mopTensorUnderlyingIso M N).hom =
      (A.X ◁ (mopTensorUnderlyingIso M N).hom) ≫
        (tensorBimod (mopBimodule N) (mopBimodule M)).actRight.unmop := by
  refine (cancel_epi ((tensorLeft A.X).map
    (coequalizer.π (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft)))).mp ?_
  change (A.X ◁ tensorProjection M N) ≫ (tensorBimod M N).actLeft ≫ (mopTensorUnderlyingIso M N).hom =
    (A.X ◁ tensorProjection M N) ≫ (A.X ◁ (mopTensorUnderlyingIso M N).hom) ≫
      (tensorBimod (mopBimodule N) (mopBimodule M)).actRight.unmop
  rw [tensorProjection_leftAction_assoc, mopTensorUnderlyingIso_projection,
    ← whiskerLeft_comp_assoc, mopTensorUnderlyingIso_projection]
  have h := congrArg Quiver.Hom.unmop (tensorProjection_rightAction (mopBimodule N) (mopBimodule M))
  change (A.X ◁ (CategoryTheory.unmopFunctor C).map
      (tensorProjection (mopBimodule N) (mopBimodule M))) ≫
      (tensorBimod (mopBimodule N) (mopBimodule M)).actRight.unmop =
    (α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X) ≫
      (CategoryTheory.unmopFunctor C).map
        (tensorProjection (mopBimodule N) (mopBimodule M)) at h
  exact h.symm

/-- Both whole original tensor actions are preserved by the actual opposite tensor isomorphism. -/
def mopTensorIso (M : Bimod A B) (N : Bimod B D) :
    mopBimodule (tensorBimod M N) ≅ tensorBimod (mopBimodule N) (mopBimodule M) :=
  isoOfIso ((CategoryTheory.mopFunctor C).mapIso (mopTensorUnderlyingIso M N))
    (by apply Quiver.Hom.unmop_inj; exact mopTensorUnderlyingIso_rightAction M N)
    (by apply Quiver.Hom.unmop_inj; exact mopTensorUnderlyingIso_leftAction M N)

/-- The complete opposite tensor comparison keeps its original unwrapped coequalizer map. -/
theorem mopTensorIso_hom_unmop (M : Bimod A B) (N : Bimod B D) :
    (mopTensorIso M N).hom.hom.unmop = (mopTensorUnderlyingIso M N).hom := rfl

/-- Every pair of original bimodule maps is natural on the entire opposite tensor comparison. -/
theorem mopTensorIso_naturality {M M' : Bimod A B} {N N' : Bimod B D} (f : M ⟶ M') (g : N ⟶ N') :
    mopBimoduleMap (tensorMap f g) ≫ (mopTensorIso M' N').hom =
      (mopTensorIso M N).hom ≫ tensorMap (mopBimoduleMap g) (mopBimoduleMap f) := by
  apply Bimod.hom_ext
  apply Quiver.Hom.unmop_inj
  apply coequalizer.hom_ext
  have h := congrArg Quiver.Hom.unmop (tensorMap_projection (mopBimoduleMap g) (mopBimoduleMap f))
  change (CategoryTheory.unmopFunctor C).map
      (tensorProjection (mopBimodule N) (mopBimodule M)) ≫
      (tensorMap (mopBimoduleMap g) (mopBimoduleMap f)).hom.unmop =
    (f.hom ⊗ₘ g.hom) ≫ (CategoryTheory.unmopFunctor C).map
      (tensorProjection (mopBimodule N') (mopBimodule M')) at h
  change tensorProjection M N ≫ (tensorMap f g).hom ≫ (mopTensorUnderlyingIso M' N').hom =
    tensorProjection M N ≫ (mopTensorUnderlyingIso M N).hom ≫
      (tensorMap (mopBimoduleMap g) (mopBimoduleMap f)).hom.unmop
  rw [← Category.assoc, tensorMap_projection, Category.assoc, mopTensorUnderlyingIso_projection,
    ← Category.assoc, mopTensorUnderlyingIso_projection, h]

/-- The complete fixed-left tensor comparison is natural on every original right bimodule. -/
def mopTensorLeftNatIso (M : Bimod A B) :
    tensorLeftFunctor (D := D) M ⋙ mopFunctor A D ≅
      mopFunctor B D ⋙ tensorRightFunctor (A := mopMon D) (mopBimodule M) :=
  NatIso.ofComponents (mopTensorIso M) (by
    intro N N' g
    have h := mopTensorIso_naturality (𝟙 M) g
    have hi : mopBimoduleMap (𝟙 M) = 𝟙 (mopBimodule M) := by apply Bimod.hom_ext; rfl
    rw [hi] at h
    simp only [tensorMap, id_whiskerRight_bimod, whiskerLeft_id_bimod, Category.id_comp,
      Category.comp_id] at h
    exact h)

end Bimod
