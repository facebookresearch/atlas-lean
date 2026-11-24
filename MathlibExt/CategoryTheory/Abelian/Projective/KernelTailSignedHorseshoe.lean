/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.Projective.KernelTailSignedComplex
public import MathlibExt.Algebra.Homology.ProjectiveResolutionAugment
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The signed kernel-tail horseshoe and its augmentation
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]


set_option backward.isDefEq.respectTransparency false in
/-- The kernel sequence of the original projective augmentation is short exact. -/
theorem normalizationKernelSequence_shortExact {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.kernelSequence (P.π.f 0)).ShortExact := by
  let _ : Epi (P.π.f 0) := epi_of_isColimit_cofork P.isColimitCokernelCofork
  exact { exact := ShortComplex.kernelSequence_exact (P.π.f 0)
          epi_g := by change Epi (P.π.f 0); infer_instance }

/-- The left inclusion into the alternating-cross middle complex. -/
def normalizationMiddleInclusion {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTail P).complex ⟶ normalizationMiddleComplex P :=
  ChainComplex.ofHom (fun _ => biprod.inl) (fun n => by
    dsimp only [normalizationMiddleComplex]
    rw [ChainComplex.of_d, normalizationMiddleDifferential]
    rw [Biprod.inl_ofComponents]
    simp)

/-- The right projection from the alternating-cross middle complex. -/
def normalizationMiddleProjection {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleComplex P ⟶ P.complex :=
  ChainComplex.ofHom (fun _ => biprod.snd) (fun n => by
    dsimp only [normalizationMiddleComplex]
    rw [ChainComplex.of_d, normalizationMiddleDifferential]
    rw [Biprod.ofComponents_snd]
    simp)

/-- The two complex maps form a complex. -/
theorem normalizationMiddleInclusion_comp_projection {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleInclusion P ≫ normalizationMiddleProjection P = 0 := by
  ext n
  exact biprod.inl_snd

/-- The resolution complexes form a degreewise split short exact sequence. -/
theorem normalizationMiddleComplex_shortExact {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.mk (normalizationMiddleInclusion P)
      (normalizationMiddleProjection P)
          (normalizationMiddleInclusion_comp_projection P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro n
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct
    ((normalizationKernelTail P).complex.X n) (P.complex.X n)).shortExact

/-- The original degree-zero augmentation of the middle complex. -/
def normalizationMiddleAugmentationZero {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleComplex P).X 0 ⟶ P.complex.X 0 :=
  biprod.desc ((normalizationKernelTail P).π.f 0 ≫ kernel.ι (P.π.f 0))
    (𝟙 (P.complex.X 0))

set_option backward.isDefEq.respectTransparency false in
/-- The original augmentation satisfies the chain condition with cross coefficient -1. -/
theorem normalizationMiddleAugmentationZero_condition {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleComplex P).d 1 0 ≫ normalizationMiddleAugmentationZero P = 0 := by
  rw [normalizationMiddleComplex_d, normalizationMiddleDifferential]
  apply biprod.hom_ext'
  · rw [← Category.assoc, Biprod.inl_ofComponents]
    simp [normalizationMiddleAugmentationZero, Category.assoc]
  · rw [← Category.assoc, Biprod.inr_ofComponents]
    have h₀ : (normalizationKernelTailXIso P 0).inv = 𝟙 (P.complex.X 1) := rfl
    simp [normalizationMiddleAugmentationZero, normalizationCross, normalizationCrossSign,
      h₀, normalizationKernelTail_π_f_zero, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The original augmentation commutes with the original right augmentation. -/
theorem normalizationMiddleAugmentationZero_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleAugmentationZero P ≫ P.π.f 0 = biprod.snd ≫ P.π.f 0 := by
  apply biprod.hom_ext'
  · simp [normalizationMiddleAugmentationZero, Category.assoc]
  · simp [normalizationMiddleAugmentationZero]

/-- The original middle augmentation to a single complex. -/
def normalizationMiddleπ {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleComplex P ⟶ (ChainComplex.single₀ C).obj (P.complex.X 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨normalizationMiddleAugmentationZero P, normalizationMiddleAugmentationZero_condition P⟩

/-- The augmentation retains its literal degree-zero arrow. -/
theorem normalizationMiddleπ_f_zero {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleπ P).f 0 = normalizationMiddleAugmentationZero P :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- The left inclusion preserves the original augmentation. -/
theorem normalizationMiddleInclusion_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleInclusion P ≫ normalizationMiddleπ P =
      (normalizationKernelTail P).π ≫ (ChainComplex.single₀ C).map (kernel.ι (P.π.f 0)) := by
  ext
  simp only [HomologicalComplex.comp_f, normalizationMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact biprod.inl_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The right projection preserves the original augmentation. -/
theorem normalizationMiddleProjection_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleProjection P ≫ P.π =
      normalizationMiddleπ P ≫ (ChainComplex.single₀ C).map (P.π.f 0) := by
  ext
  simp only [HomologicalComplex.comp_f, normalizationMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact (normalizationMiddleAugmentationZero_comp_π P).symm

/-- The middle complex augmented by the original middle object. -/
def normalizationMiddleAugmented {X : C} (P : ProjectiveResolution X) : ChainComplex C ℕ :=
  (normalizationMiddleComplex P).augment (normalizationMiddleAugmentationZero P)
    (normalizationMiddleAugmentationZero_condition P)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion on augmented complexes uses the original kernel inclusion in degree zero. -/
def normalizationAugmentedInclusion {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTail P).augmented ⟶ normalizationMiddleAugmented P :=
  ChainComplex.ofHom
    (fun | 0 => kernel.ι (P.π.f 0) | n + 1 => (normalizationMiddleInclusion P).f n)
    (fun n => by
      cases n with
      | zero =>
          change biprod.inl ≫ normalizationMiddleAugmentationZero P =
            (normalizationKernelTail P).π.f 0 ≫ kernel.ι (P.π.f 0)
          exact biprod.inl_desc _ _
      | succ n =>
          simpa only [Nat.add_one, augmented, normalizationMiddleAugmented,
            ChainComplex.augment_d_succ_succ] using (normalizationMiddleInclusion P).comm (n + 1) n)

set_option backward.isDefEq.respectTransparency false in
/-- The projection on augmented complexes uses the original augmentation in degree zero. -/
def normalizationAugmentedProjection {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleAugmented P ⟶ P.augmented :=
  ChainComplex.ofHom
    (fun | 0 => P.π.f 0 | n + 1 => (normalizationMiddleProjection P).f n)
    (fun n => by
      cases n with
      | zero =>
          change biprod.snd ≫ P.π.f 0 =
            normalizationMiddleAugmentationZero P ≫ P.π.f 0
          exact (normalizationMiddleAugmentationZero_comp_π P).symm
      | succ n =>
          simpa only [Nat.add_one, augmented, normalizationMiddleAugmented,
            ChainComplex.augment_d_succ_succ] using
                (normalizationMiddleProjection P).comm (n + 1) n)

/-- The augmented maps retain the literal kernel-sequence zero relation. -/
theorem normalizationAugmentedInclusion_comp_projection {X : C} (P : ProjectiveResolution X) :
    normalizationAugmentedInclusion P ≫ normalizationAugmentedProjection P = 0 := by
  ext (_ | n)
  · exact kernel.condition (P.π.f 0)
  · exact biprod.inl_snd

set_option backward.isDefEq.respectTransparency false in
/-- The original augmented kernel sequence and positive split degrees are short exact. -/
theorem normalizationAugmented_shortExact {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.mk (normalizationAugmentedInclusion P) (normalizationAugmentedProjection P)
      (normalizationAugmentedInclusion_comp_projection P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro n
  cases n with
  | zero =>
      change (ShortComplex.kernelSequence (P.π.f 0)).ShortExact
      exact normalizationKernelSequence_shortExact P
  | succ n =>
      change (ShortComplex.mk
        (biprod.inl : (normalizationKernelTail P).complex.X n ⟶
          (normalizationKernelTail P).complex.X n ⊞ P.complex.X n)
        (biprod.snd : (normalizationKernelTail P).complex.X n ⊞ P.complex.X n ⟶ P.complex.X n)
        biprod.inl_snd).ShortExact
      exact (ShortComplex.Splitting.ofHasBinaryBiproduct
        ((normalizationKernelTail P).complex.X n) (P.complex.X n)).shortExact

/-- The augmented middle complex is acyclic by the two endpoint resolutions. -/
theorem normalizationMiddleAugmented_acyclic {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleAugmented P).Acyclic :=
  (normalizationAugmented_shortExact P).acyclic_X₂
    (normalizationKernelTail P).augmented_acyclic P.augmented_acyclic

/-- The middle augmentation is a quasi-isomorphism. -/
theorem normalizationMiddleπ_quasiIso {X : C} (P : ProjectiveResolution X) :
    QuasiIso (normalizationMiddleπ P) :=
  ChainComplex.quasiIso_toSingle₀_of_augment_acyclic
    (normalizationMiddleComplex P) (P.complex.X 0)
    (normalizationMiddleAugmentationZero P) (normalizationMiddleAugmentationZero_condition P)
    (normalizationMiddleAugmented_acyclic P)

/-- The alternating-cross horseshoe resolves the original projective degree-zero object. -/
def normalizationMiddleResolution {X : C} (P : ProjectiveResolution X) :
    ProjectiveResolution (P.complex.X 0) where
  complex := normalizationMiddleComplex P
  projective n := by
    change Projective ((normalizationKernelTail P).complex.X n ⊞ P.complex.X n)
    infer_instance
  π := normalizationMiddleπ P
  quasiIso := normalizationMiddleπ_quasiIso P

/-- The signed kernel-tail horseshoe, retaining both original augmented endpoint maps. -/
def normalizationKernelTailHorseshoe {X : C} (P : ProjectiveResolution X) :
    HorseshoeData (normalizationKernelSequence_shortExact P) (normalizationKernelTail P) P where
  middle := normalizationMiddleResolution P
  i := normalizationMiddleInclusion P
  p := normalizationMiddleProjection P
  zero := normalizationMiddleInclusion_comp_projection P
  shortExact := normalizationMiddleComplex_shortExact P
  i_augmentation := normalizationMiddleInclusion_comp_π P
  p_augmentation := normalizationMiddleProjection_comp_π P

set_option backward.isDefEq.respectTransparency false in
/-- The signed horseshoe has the stock biproduct coordinate specification. -/
def normalizationKernelTailHorseshoeSpec {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTailHorseshoe P).Spec where
  middleXIso _ := Iso.refl _
  i_f _ := Category.comp_id _
  p_f _ := Category.id_comp _
  middle_d n := by
    dsimp only [normalizationKernelTailHorseshoe, normalizationMiddleResolution,
      ShortComplex.kernelSequence,
      Iso.refl_inv, Iso.refl_hom, normalizationMiddleComplex]
    simp only [Category.id_comp, Category.comp_id, ChainComplex.of_d]
    simp [normalizationMiddleDifferential, Biprod.ofComponents]

end CategoryTheory.ProjectiveResolution
