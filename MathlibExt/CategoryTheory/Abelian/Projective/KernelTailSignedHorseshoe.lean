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
# Augmented alternating-cross kernel-tail horseshoe

Let `P` resolve `X` in an abelian category, `K=ker(P₀ → X)`,
`T` its kernel-tail resolution, and `M_n=T_n ⊞ P_n` the alternating-
cross middle complex. Its augmentation to `P₀` is
`[T₀ → K → P₀, id]`. The kernel inclusion and original augmentation
extend the degreewise split complex row to an augmented short exact
sequence. Its middle augmented complex is acyclic, so `M` resolves
`P₀` and gives a horseshoe for `K → P₀ → X`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]


set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The sequence `K → P₀ → X` is short exact, since the
projective-resolution augmentation `π₀` is epi. -/
theorem normalizationKernelSequence_shortExact {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.kernelSequence (P.π.f 0)).ShortExact := by
  let _ : Epi (P.π.f 0) := epi_of_isColimit_cofork P.isColimitCokernelCofork
  exact { exact := ShortComplex.kernelSequence_exact (P.π.f 0)
          epi_g := by change Epi (P.π.f 0); infer_instance }

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The left biproduct inclusions in every degree give a chain
map `T → M` into the alternating-cross middle complex. -/
def normalizationMiddleInclusion {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTail P).complex ⟶ normalizationMiddleComplex P :=
  ChainComplex.ofHom (fun _ => biprod.inl) (fun n => by
    dsimp only [normalizationMiddleComplex]
    rw [ChainComplex.of_d, normalizationMiddleDifferential]
    rw [Biprod.inl_ofComponents]
    simp)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The right biproduct projections in every degree give a
chain map `M → P` from the alternating-cross middle complex. -/
def normalizationMiddleProjection {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleComplex P ⟶ P.complex :=
  ChainComplex.ofHom (fun _ => biprod.snd) (fun n => by
    dsimp only [normalizationMiddleComplex]
    rw [ChainComplex.of_d, normalizationMiddleDifferential]
    rw [Biprod.ofComponents_snd]
    simp)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The chain inclusion `T → M` followed by the projection
`M → P` is zero, because left inclusion and right projection have
zero composite in each degree. -/
theorem normalizationMiddleInclusion_comp_projection {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleInclusion P ≫ normalizationMiddleProjection P = 0 := by
  ext n
  exact biprod.inl_snd

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The chain row `T → M → P` is short exact: each degree
is the split row `T_n → T_n ⊞ P_n → P_n`. -/
theorem normalizationMiddleComplex_shortExact {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.mk (normalizationMiddleInclusion P)
      (normalizationMiddleProjection P)
          (normalizationMiddleInclusion_comp_projection P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro n
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct
    ((normalizationKernelTail P).complex.X n) (P.complex.X n)).shortExact

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The middle degree-zero augmentation `a₀ : M₀ → P₀`
is `[π_T ≫ (K → P₀), 𝟙 P₀]` on `M₀=T₀ ⊞ P₀`. -/
def normalizationMiddleAugmentationZero {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleComplex P).X 0 ⟶ P.complex.X 0 :=
  biprod.desc ((normalizationKernelTail P).π.f 0 ≫ kernel.ι (P.π.f 0))
    (𝟙 (P.complex.X 0))

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. For the augmentation `a₀ : M₀ → P₀`, the differential
`M₁ → M₀` followed by `a₀` is zero; the degree-zero cross
coefficient is `-1`. -/
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
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The middle augmentation satisfies
`a₀ ≫ π₀ = biprod.snd ≫ π₀`, because the left component factors
through `ker(π₀)`. -/
theorem normalizationMiddleAugmentationZero_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleAugmentationZero P ≫ P.π.f 0 = biprod.snd ≫ P.π.f 0 := by
  apply biprod.hom_ext'
  · simp [normalizationMiddleAugmentationZero, Category.assoc]
  · simp [normalizationMiddleAugmentationZero]

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The middle augmentation `a₀ : M₀ → P₀` defines a chain
map `M → P₀[0]` to the complex concentrated in degree zero. -/
def normalizationMiddleπ {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleComplex P ⟶ (ChainComplex.single₀ C).obj (P.complex.X 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨normalizationMiddleAugmentationZero P, normalizationMiddleAugmentationZero_condition P⟩

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The degree-zero component of the chain augmentation
`M → P₀[0]` is the map `[π_T ≫ (K → P₀), 𝟙 P₀]`. -/
theorem normalizationMiddleπ_f_zero {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleπ P).f 0 = normalizationMiddleAugmentationZero P :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The chain inclusion `T → M`, followed by `M → P₀[0]`,
equals the augmentation `T → K[0]` followed by the kernel
inclusion concentrated in degree zero. -/
theorem normalizationMiddleInclusion_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleInclusion P ≫ normalizationMiddleπ P =
      (normalizationKernelTail P).π ≫ (ChainComplex.single₀ C).map (kernel.ι (P.π.f 0)) := by
  ext
  simp only [HomologicalComplex.comp_f, normalizationMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact biprod.inl_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The projection `M → P`, followed by `P → X[0]`, equals
the augmentation `M → P₀[0]` followed by `π₀` concentrated in
degree zero. -/
theorem normalizationMiddleProjection_comp_π {X : C} (P : ProjectiveResolution X) :
    normalizationMiddleProjection P ≫ P.π =
      normalizationMiddleπ P ≫ (ChainComplex.single₀ C).map (P.π.f 0) := by
  ext
  simp only [HomologicalComplex.comp_f, normalizationMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact (normalizationMiddleAugmentationZero_comp_π P).symm

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. Adjoining `P₀` in degree zero to `M` gives the augmented
middle complex, with degree-`n+1` term `M_n` and first
differential `a₀ : M₀ → P₀`. -/
def normalizationMiddleAugmented {X : C} (P : ProjectiveResolution X) : ChainComplex C ℕ :=
  (normalizationMiddleComplex P).augment (normalizationMiddleAugmentationZero P)
    (normalizationMiddleAugmentationZero_condition P)

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmented chain inclusion has the kernel inclusion
`K → P₀` in degree zero and the biproduct inclusion `T_n → M_n`
in degree `n+1`. -/
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
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmented chain projection has `π₀ : P₀ → X` in
degree zero and the right biproduct projection `M_n → P_n`
in degree `n+1`. -/
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

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmented inclusion followed by the augmented projection
is zero: in degree zero this is `(K → P₀) ≫ π₀=0`, and in positive
degrees it is left inclusion followed by right projection. -/
theorem normalizationAugmentedInclusion_comp_projection {X : C} (P : ProjectiveResolution X) :
    normalizationAugmentedInclusion P ≫ normalizationAugmentedProjection P = 0 := by
  ext (_ | n)
  · exact kernel.condition (P.π.f 0)
  · exact biprod.inl_snd

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmented row `T_aug → M_aug → P_aug` is short exact:
its degree-zero row is `K → P₀ → X`, and its positive-degree rows
are the split biproduct rows. -/
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

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmented middle complex is acyclic, since it lies in
a short exact sequence with the acyclic augmented resolutions of
`K` and `X`. -/
theorem normalizationMiddleAugmented_acyclic {X : C} (P : ProjectiveResolution X) :
    (normalizationMiddleAugmented P).Acyclic :=
  (normalizationAugmented_shortExact P).acyclic_X₂
    (normalizationKernelTail P).augmented_acyclic P.augmented_acyclic

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The middle augmentation `M → P₀[0]` is a quasi-isomorphism,
since its augmented complex is acyclic. -/
theorem normalizationMiddleπ_quasiIso {X : C} (P : ProjectiveResolution X) :
    QuasiIso (normalizationMiddleπ P) :=
  ChainComplex.quasiIso_toSingle₀_of_augment_acyclic
    (normalizationMiddleComplex P) (P.complex.X 0)
    (normalizationMiddleAugmentationZero P) (normalizationMiddleAugmentationZero_condition P)
    (normalizationMiddleAugmented_acyclic P)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The alternating-cross middle complex `M`, augmented by
`[π_T ≫ (K → P₀), 𝟙 P₀]`, is a projective resolution of `P₀`. -/
def normalizationMiddleResolution {X : C} (P : ProjectiveResolution X) :
    ProjectiveResolution (P.complex.X 0) where
  complex := normalizationMiddleComplex P
  projective n := by
    change Projective ((normalizationKernelTail P).complex.X n ⊞ P.complex.X n)
    infer_instance
  π := normalizationMiddleπ P
  quasiIso := normalizationMiddleπ_quasiIso P

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The resolutions `T,M,P` and their compatible augmented
inclusion and projection form horseshoe data for the kernel
sequence `K → P₀ → X`. -/
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
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The signed horseshoe has biproduct coordinates `M_n=T_n ⊞ P_n`,
left inclusion, right projection, diagonal differentials `d_T,d_P`,
and the alternating kernel-tail cross maps. -/
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
