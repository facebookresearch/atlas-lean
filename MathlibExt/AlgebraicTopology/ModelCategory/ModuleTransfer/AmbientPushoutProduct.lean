/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AmbientTensorHomParametrized
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# The full ambient pushout-product laws on associative modules

The ambient coefficient belongs to the original base category and both
module variables belong to the original associative module category.
Forgetting the entire actual cotensor pullback gives the base pullback-Hom
Arrow. The original parametrized lifting equivalence then earns all three
ambient pushout-product laws in the created module model. The scalar is
arbitrary; no scalar cofibrancy or relative-flatness outcome is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra Opposite
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.AmbientPushoutProduct

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] [ModelCategory (Mod C A)]

open CategoryTheory.HomogeneousLocalization.AmbientTensorHom

/-- The forgetful functor creates the small limits used to form module cotensor pullbacks. -/
local instance forgetCreatesLimits : CreatesLimitsOfSize.{0, 0} (Mod.forget (D := C) A) :=
  Mod.forgetCreatesLimits.{0} A

/-- The entire original module cotensor square forgets to the original base internal-Hom pullback. -/
def forgottenPullbackPacket {U V : C} (f : U ⟶ V) {M N : Mod C A} (p : M ⟶ N)
    (R : (rightBifunctor A).PullbackObjObj f p) :
    MonoidalClosed.internalHom.PullbackObjObj f p.hom where
  pt := R.pt.X
  fst := R.fst.hom
  snd := R.snd.hom
  isPullback := (Mod.forget (D := C) A).map_isPullback R.isPullback
  π := R.π.hom
  π_fst := congrArg (fun q => q.hom) R.π_fst
  π_snd := congrArg (fun q => q.hom) R.π_snd

/-- Both projections and the actual map into the module pullback form the whole forgotten Arrow comparison. -/
def forgetPullbackPacketIso {U V : C} (f : U ⟶ V) {M N : Mod C A} (p : M ⟶ N)
    (R : (rightBifunctor A).PullbackObjObj f p) :
    Arrow.mk R.π.hom ≅ ((op (Arrow.mk f)) ⋔ Arrow.mk p.hom) := by
  let S := forgottenPullbackPacket f p R
  let T := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom f p.hom
  let e : S.pt ≅ T.pt := S.isPullback.isoIsPullback _ _ T.isPullback
  have h₁ : e.hom ≫ T.fst = S.fst := S.isPullback.isoIsPullback_hom_fst _ _ T.isPullback
  have h₂ : e.hom ≫ T.snd = S.snd := S.isPullback.isoIsPullback_hom_snd _ _ T.isPullback
  have he : S.π ≫ e.hom = T.π := by
    apply T.isPullback.hom_ext
    · rw [Category.assoc, h₁, S.π_fst, T.π_fst]
    · rw [Category.assoc, h₂, S.π_snd, T.π_snd]
  exact Arrow.isoMk (Iso.refl _) e (by
    simp only [Iso.refl_hom, Category.id_comp, Arrow.mk_hom, MonoidalCategory.Arrow.pullbackHom]
    exact he.symm)

private theorem basePullbackHomClauses :
    PullbackHomLe (cofibrations C) (trivialFibrations C) (trivialFibrations C) ∧
      PullbackHomLe (trivialCofibrations C) (fibrations C) (trivialFibrations C) ∧
        PullbackHomLe (cofibrations C) (fibrations C) (fibrations C) := by
  refine ⟨?_, ?_, ?_⟩
  · have h : PushoutProductLe (cofibrations C) (cofibrations C) (trivialFibrations C).llp := by
      rw [trivialFibrations_llp]
      exact IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    simpa only [cofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (cofibrations C) (cofibrations C) (trivialFibrations C)).mp h
  · have h : PushoutProductLe (trivialCofibrations C) (cofibrations C) (fibrations C).llp := by
      rw [fibrations_llp]
      exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    simpa only [cofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (trivialCofibrations C) (cofibrations C) (fibrations C)).mp h
  · have h : PushoutProductLe (cofibrations C) (trivialCofibrations C) (fibrations C).llp := by
      rw [fibrations_llp]
      exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    simpa only [trivialCofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (cofibrations C) (trivialCofibrations C) (fibrations C)).mp h

/-- Created classes and the whole actual forgotten square give the first trivial cotensor law. -/
theorem pullback_trivial
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (p : M ⟶ N)
    (R : (rightBifunctor A).PullbackObjObj f p)
    (hf : cofibrations C f) (hp : trivialFibrations (Mod C A) p) :
    trivialFibrations (Mod C A) R.π := by
  have hpC : trivialFibrations C p.hom := by
    change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) p at hp
    rw [hF, hW] at hp
    exact hp
  change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) R.π
  rw [hF, hW]
  change trivialFibrations C R.π.hom
  exact ((trivialFibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHomClauses.1 f p.hom hf hpC)

/-- Every original coefficient cofibration gives the actual cotensor fibration law. -/
theorem pullback_fibration
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (p : M ⟶ N)
    (R : (rightBifunctor A).PullbackObjObj f p)
    (hf : cofibrations C f) (hp : fibrations (Mod C A) p) : fibrations (Mod C A) R.π := by
  rw [hF] at hp ⊢
  change fibrations C R.π.hom
  exact ((fibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHomClauses.2.2 f p.hom hf hp)

/-- Triviality of the original coefficient cofibration gives the second trivial cotensor law. -/
theorem pullback_trivial_coefficient
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (p : M ⟶ N)
    (R : (rightBifunctor A).PullbackObjObj f p)
    (hf : trivialCofibrations C f) (hp : fibrations (Mod C A) p) :
    trivialFibrations (Mod C A) R.π := by
  rw [hF] at hp
  change (fibrations (Mod C A) ⊓ weakEquivalences (Mod C A)) R.π
  rw [hF, hW]
  change trivialFibrations C R.π.hom
  exact ((trivialFibrations C).arrow_mk_iso_iff (forgetPullbackPacketIso f p R)).mpr
    (basePullbackHomClauses.2.1 f p.hom hf hp)

/-- The actual ambient tensor is a cofibration bifunctor in the original created module model. -/
theorem cofibration
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (g : M ⟶ N)
    (hf : cofibrations C f) (hg : cofibrations (Mod C A) g) :
    cofibrations (Mod C A) (((ambientPushoutProduct A).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (leftBifunctor A) f g
  change cofibrations (Mod C A) R.ι
  rw [← trivialFibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (rightBifunctor A) f p
  apply ((parametrizedAdjunction A).hasLiftingProperty_iff R S).mpr
  rw [← trivialFibrations_llp] at hg
  exact hg S.π (pullback_trivial hW hF f p S hf hp)

/-- The original trivial ambient coefficient law is earned through the actual parametrized adjunction. -/
theorem trivial_coefficient
    (hW : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (g : M ⟶ N)
    (hf : trivialCofibrations C f) (hg : cofibrations (Mod C A) g) :
    trivialCofibrations (Mod C A) (((ambientPushoutProduct A).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (leftBifunctor A) f g
  change trivialCofibrations (Mod C A) R.ι
  rw [← fibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (rightBifunctor A) f p
  apply ((parametrizedAdjunction A).hasLiftingProperty_iff R S).mpr
  rw [← trivialFibrations_llp] at hg
  exact hg S.π (pullback_trivial_coefficient hW hF f p S hf hp)

/-- The original trivial module-variable law is earned without any scalar cofibrancy premise. -/
theorem trivial_module
    (hF : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    {U V : C} (f : U ⟶ V) {M N : Mod C A} (g : M ⟶ N)
    (hf : cofibrations C f) (hg : trivialCofibrations (Mod C A) g) :
    trivialCofibrations (Mod C A) (((ambientPushoutProduct A).obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let R := Functor.PushoutObjObj.ofHasPushout (leftBifunctor A) f g
  change trivialCofibrations (Mod C A) R.ι
  rw [← fibrations_llp]
  intro X Y p hp
  let S := Functor.PullbackObjObj.ofHasPullback (rightBifunctor A) f p
  apply ((parametrizedAdjunction A).hasLiftingProperty_iff R S).mpr
  rw [← fibrations_llp] at hg
  exact hg S.π (pullback_fibration hF f p S hf hp)

end HomotopicalAlgebra.ModuleTransfer.AmbientPushoutProduct
