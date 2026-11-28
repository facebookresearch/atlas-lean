/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.SpectralObject.Page
public import Mathlib.CategoryTheory.Abelian.Exact
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotient

/-!
# Stable spectral intervals as ordered image quotients

Let Y be a spectral object in an abelian category D over a preorder ι with bottom and top. For
n∈ℤ write A_i=H^n_Y(⊥,i), A=H^n_Y(⊥,⊤), and u_i:A_i→A for the bottom-to-top map. If i₁≤i₂, the
step map a:A_{i₁}→A_{i₂} satisfies a≫u_{i₂}=u_{i₁}, giving an inclusion j:image u_{i₁}→image
u_{i₂}.

The stable interval E_Y(⊥,i₁,i₂,⊤;n) is the cokernel of [a,δ]:A_{i₁}⊕H^{n-1}_Y(i₂,⊤)→A_{i₂},
where δ is the connecting map into degree n. Its quotient π descends uniquely through
A_{i₂}→image u_{i₂}, because δ dies in the abutment image. The descended map q:image u_{i₂}→E is
a cokernel of j. Consequently E≅coker j canonically, with q followed by the comparison equal to
the cokernel projection. Object, morphism and index universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]
variable {ι : Type w} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (Y : SpectralObject D ι)

def stableIntervalLeft (i₁ : ι) : (⊥ : ι) ⟶ i₁ :=
  homOfLE bot_le

def stableIntervalMiddle {i₁ i₂ : ι} (h : i₁ ≤ i₂) : i₁ ⟶ i₂ :=
  homOfLE h

def stableIntervalRight (i₂ : ι) : i₂ ⟶ (⊤ : ι) :=
  homOfLE le_top

/-- Compatibility name for the unique bottom-to-cut arrow. -/
abbrev stableIntervalLeftMiddle (i₂ : ι) : (⊥ : ι) ⟶ i₂ :=
  stableIntervalLeft i₂

def stableIntervalFull : (⊥ : ι) ⟶ (⊤ : ι) :=
  homOfLE bot_le

omit [OrderTop ι] in
theorem stableIntervalLeft_comp_middle {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    stableIntervalLeft i₁ ≫ stableIntervalMiddle h =
      stableIntervalLeftMiddle i₂ :=
  Subsingleton.elim _ _

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i∈ι, this step object is A_i=H^n_Y(⊥,i), the degree-n spectral value
on the unique arrow ⊥→i. The bottom cut and the chosen cut determine the interval; no choice of
a spectral page enters this object. -/
noncomputable def stableIntervalStep (n : ℤ) (i : ι) : D :=
  (Y.H n).obj (mk₁ (stableIntervalLeftMiddle i))

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ, the abutment object is A=H^n_Y(⊥,⊤), the degree-n spectral value of the
full index interval. It is the common target of the bottom-to-cut step maps. -/
noncomputable def stableIntervalAbutment (n : ℤ) : D :=
  (Y.H n).obj (mk₁ stableIntervalFull)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, this is the map a:H^n_Y(⊥,i₁)→H^n_Y(⊥,i₂) induced by the
interval square with identity on bottom and the arrow i₁→i₂ on the other endpoint. If u_i maps
the step to H^n_Y(⊥,⊤), then a≫u_{i₂}=u_{i₁}. -/
noncomputable def stableIntervalStepMap
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₁ ⟶ Y.stableIntervalStep n i₂ :=
  (Y.H n).map
    (twoδ₂Toδ₁
      (stableIntervalLeft i₁)
      (stableIntervalMiddle h)
      (stableIntervalLeftMiddle i₂)
      (stableIntervalLeft_comp_middle h))

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i∈ι, this is u_i:H^n_Y(⊥,i)→H^n_Y(⊥,⊤), induced by identity on bottom
and i→⊤ on the upper endpoint. It supplies the ambient map whose image defines the cut's
abutment subobject. -/
noncomputable def stableIntervalStepToAbutment (n : ℤ) (i : ι) :
    Y.stableIntervalStep n i ⟶ Y.stableIntervalAbutment n :=
  (Y.H n).map
    (homMk₁ (𝟙 _) (stableIntervalRight i) (by subsingleton))

@[reassoc]
theorem stableIntervalStepMap_comp_toAbutment
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToAbutment n i₂ =
      Y.stableIntervalStepToAbutment n i₁ := by
  dsimp only [stableIntervalStepMap, stableIntervalStepToAbutment]
  rw [← Functor.map_comp]
  apply (Y.H n).congr_map
  subsingleton

noncomputable abbrev stableIntervalStepImage (n : ℤ) (i : ι) : D :=
  Limits.image (Y.stableIntervalStepToAbutment n i)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i∈ι, let u_i:A_i=H^n_Y(⊥,i)→A=H^n_Y(⊥,⊤). This is the canonical
epimorphism e_i:A_i→image u_i in its image factorization. It satisfies e_i≫image.ι(u_i)=u_i. -/
noncomputable def stableIntervalStepToImage (n : ℤ) (i : ι) :
    Y.stableIntervalStep n i ⟶
      Limits.image (Y.stableIntervalStepToAbutment n i) :=
  Limits.factorThruImage (Y.stableIntervalStepToAbutment n i)

instance stableIntervalStepToImage_epi (n : ℤ) (i : ι) :
    Epi (Y.stableIntervalStepToImage n i) := by
  dsimp only [stableIntervalStepToImage]
  infer_instance

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, write u_i:H^n_Y(⊥,i)→H^n_Y(⊥,⊤). The relation a≫u_{i₂}=u_{i₁}
for the step map a induces this map j:image u_{i₁}→image u_{i₂}. It is the inclusion of these
selected image subobjects and satisfies j≫image.ι(u_{i₂})=image.ι(u_{i₁}). -/
noncomputable def stableIntervalImageMap
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₁) ⟶
      Limits.image (Y.stableIntervalStepToAbutment n i₂) :=
  (Limits.image.eqToIso
    (Y.stableIntervalStepMap_comp_toAbutment n h).symm).hom ≫
  Limits.image.preComp
    (Y.stableIntervalStepMap n h)
    (Y.stableIntervalStepToAbutment n i₂)

@[reassoc]
theorem stableIntervalImageMap_comp_ι
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Limits.image.ι (Y.stableIntervalStepToAbutment n i₂) =
      Limits.image.ι (Y.stableIntervalStepToAbutment n i₁) := by
  dsimp only [stableIntervalImageMap]
  rw [Category.assoc, Limits.image.preComp_ι]
  exact (Limits.image.eq_fac
    (Y.stableIntervalStepMap_comp_toAbutment n h).symm).symm

@[reassoc]
theorem stableIntervalStepToImage_naturality
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToImage n i₂ =
      Y.stableIntervalStepToImage n i₁ ≫
        Y.stableIntervalImageMap n h := by
  apply (cancel_mono
    (Limits.image.ι (Y.stableIntervalStepToAbutment n i₂))).1
  simp only [stableIntervalStepToImage, Category.assoc, Limits.image.fac,
    Y.stableIntervalImageMap_comp_ι n h,
    Y.stableIntervalStepMap_comp_toAbutment n h]

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, this object is E_Y(⊥,i₁,i₂,⊤;n). It uses the three successive
index arrows ⊥→i₁→i₂→⊤ and the spectral degrees n−1,n,n+1, with connecting maps increasing
degree by one. -/
noncomputable def stableIntervalObj
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : D :=
  Y.E
    (stableIntervalLeft i₁)
    (stableIntervalMiddle h)
    (stableIntervalRight i₂)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, write A_i=H^n_Y(⊥,i), a:A_{i₁}→A_{i₂}, and
δ:H^{n-1}_Y(i₂,⊤)→A_{i₂}. This is the canonical cokernel short complex A_{i₁}⊕H^{n-1}_Y(i₂,⊤)
--[a,δ]→ A_{i₂} --π→ E_Y(⊥,i₁,i₂,⊤;n). Its incoming maps are the ordered step map and the
degree-one connecting map. -/
noncomputable def stableIntervalCokernelSequence
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : ShortComplex D :=
  Y.cokernelSequenceE
    (stableIntervalLeft i₁)
    (stableIntervalMiddle h)
    (stableIntervalRight i₂)
    (stableIntervalLeftMiddle i₂)
    (stableIntervalLeft_comp_middle h)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, this is the canonical epimorphism
π:H^n_Y(⊥,i₂)→E_Y(⊥,i₁,i₂,⊤;n). It is the quotient by the ordered step map from H^n_Y(⊥,i₁) and
the connecting map from H^{n-1}_Y(i₂,⊤); both incoming maps have zero composite with π. -/
noncomputable def stableIntervalStepToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₂ ⟶ Y.stableIntervalObj n h :=
  (Y.stableIntervalCokernelSequence n h).g

instance stableIntervalStepToStable_epi
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Epi (Y.stableIntervalStepToStable n h) := by
  change Epi (Y.cokernelSequenceE
      (stableIntervalLeft i₁)
      (stableIntervalMiddle h)
      (stableIntervalRight i₂)
      (stableIntervalLeftMiddle i₂)
      (stableIntervalLeft_comp_middle h)
      (n - 1) n (n + 1) (by omega) (by omega)).g
  infer_instance

@[reassoc]
theorem stableIntervalStepMap_comp_toStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToStable n h = 0 := by
  let S := Y.stableIntervalCokernelSequence n h
  have hinl : biprod.inl ≫ S.f = Y.stableIntervalStepMap n h := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE,
      stableIntervalStepMap]
    simp only [biprod.inl_desc]
  change Y.stableIntervalStepMap n h ≫ S.g = 0
  rw [← hinl]
  exact (calc
    (biprod.inl ≫ S.f) ≫ S.g =
        biprod.inl ≫ (S.f ≫ S.g) := Category.assoc _ _ _
    _ = biprod.inl ≫ 0 := congrArg (fun k => biprod.inl ≫ k) S.zero
    _ = 0 := by simp)

@[reassoc]
theorem stableIntervalDelta_comp_toStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) ≫
      Y.stableIntervalStepToStable n h = 0 := by
  let S := Y.stableIntervalCokernelSequence n h
  have hinr : biprod.inr ≫ S.f =
      Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE]
    simp only [biprod.inr_desc]
  change _ ≫ S.g = 0
  rw [← hinr]
  exact (calc
    (biprod.inr ≫ S.f) ≫ S.g =
        biprod.inr ≫ (S.f ≫ S.g) := Category.assoc _ _ _
    _ = biprod.inr ≫ 0 := congrArg (fun k => biprod.inr ≫ k) S.zero
    _ = 0 := by simp)

theorem stableIntervalKernelZero (n : ℤ) (i₂ : ι) :
    Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
      (n - 1) n (by omega) ≫ Y.stableIntervalStepToAbutment n i₂ = 0 :=
  Y.zero₁ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
    (stableIntervalFull (ι := ι)) (Subsingleton.elim _ _) (n - 1) n

theorem stableIntervalKernelExact (n : ℤ) (i₂ : ι) :
    (ShortComplex.mk
      (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega))
      (Y.stableIntervalStepToAbutment n i₂) (stableIntervalKernelZero Y n i₂)).Exact :=
  Y.exact₁ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
    (stableIntervalFull (ι := ι)) (Subsingleton.elim _ _) (n - 1) n (by omega)

theorem stableIntervalCokernelSequence_exact
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    (Y.stableIntervalCokernelSequence n h).Exact :=
  Y.cokernelSequenceE_exact (stableIntervalLeft i₁) (stableIntervalMiddle h)
    (stableIntervalRight i₂) (stableIntervalLeftMiddle i₂)
    (stableIntervalLeft_comp_middle h) (n - 1) n (n + 1) (by omega) (by omega)

theorem stableIntervalCokernelSequence_f
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    (Y.stableIntervalCokernelSequence n h).f =
      biprod.desc (Y.stableIntervalStepMap n h)
        (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
          (n - 1) n (by omega)) := rfl

noncomputable def stableIntervalStepCokernelIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅ cokernel (Y.stableIntervalCokernelSequence n h).f := by
  let _ : Epi (Y.stableIntervalCokernelSequence n h).g := by
    change Epi (Y.stableIntervalStepToStable n h)
    infer_instance
  exact (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (Y.stableIntervalCokernelSequence n h).f)
    (stableIntervalCokernelSequence_exact Y n h).gIsCokernel).symm

theorem cokernel_π_stableIntervalStepCokernelIso_inv
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (Y.stableIntervalCokernelSequence n h).f ≫
      (Y.stableIntervalStepCokernelIso n h).inv = Y.stableIntervalStepToStable n h := by
  let _ : Epi (Y.stableIntervalCokernelSequence n h).g := by
    change Epi (Y.stableIntervalStepToStable n h)
    infer_instance
  simpa only [stableIntervalStepCokernelIso, stableIntervalStepToStable,
    stableIntervalObj, stableIntervalCokernelSequence, Iso.symm_inv, parallelPair_obj_one,
    Cofork.app_one_eq_π, Cofork.ofπ_pt, Cofork.π_ofπ] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (Y.stableIntervalCokernelSequence n h).f)
      (stableIntervalCokernelSequence_exact Y n h).gIsCokernel WalkingParallelPair.one)

theorem stableIntervalStepToStable_comp_stepCokernelIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepToStable n h ≫ (Y.stableIntervalStepCokernelIso n h).hom =
      cokernel.π (Y.stableIntervalCokernelSequence n h).f := by
  rw [← cokernel_π_stableIntervalStepCokernelIso_inv Y n h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, let u_{i₂}:A_{i₂}=H^n_Y(⊥,i₂)→H^n_Y(⊥,⊤), e_{i₂}:A_{i₂}→image
u_{i₂}, and π:A_{i₂}→E_Y(⊥,i₁,i₂,⊤;n). This is the pair consisting of the descended map q:image
u_{i₂}→E and its factorization equation e_{i₂}≫q=π. Exactness of the connecting sequence gives
the descent, and the epimorphism e_{i₂} makes it unique. -/
noncomputable def stableIntervalImageToStableLift
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    { q : Limits.image (Y.stableIntervalStepToAbutment n i₂) ⟶
        Y.stableIntervalObj n h //
      Y.stableIntervalStepToImage n i₂ ≫ q =
        Y.stableIntervalStepToStable n h }  := by
  let a := Y.stableIntervalStepMap n h
  let x := Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
    (n - 1) n (by omega)
  let b := Y.stableIntervalStepToAbutment n i₂
  let q := imageToBiprodQuotient a x b (stableIntervalKernelZero Y n i₂)
    (stableIntervalKernelExact Y n i₂) ≫ (Y.stableIntervalStepCokernelIso n h).inv
  refine ⟨q, ?_⟩
  dsimp only [q, stableIntervalStepToImage]
  rw [← Category.assoc, factorThruImage_imageToBiprodQuotient]
  exact cokernel_π_stableIntervalStepCokernelIso_inv Y n h

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, this is the descended epimorphism q:image
u_{i₂}→E_Y(⊥,i₁,i₂,⊤;n), where u_{i₂}:H^n_Y(⊥,i₂)→H^n_Y(⊥,⊤). With e_{i₂} the step-to-image
epimorphism and π the stable quotient, it satisfies e_{i₂}≫q=π. -/
noncomputable def stableIntervalImageToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₂) ⟶
      Y.stableIntervalObj n h :=
  (Y.stableIntervalImageToStableLift n h).1

@[reassoc (attr := simp)]
theorem stableIntervalStepToImage_comp_imageToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepToImage n i₂ ≫
        Y.stableIntervalImageToStable n h =
      Y.stableIntervalStepToStable n h :=
  (Y.stableIntervalImageToStableLift n h).2

instance stableIntervalImageToStable_epi
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Epi (Y.stableIntervalImageToStable n h) := by
  have hcomp : Epi
      (Y.stableIntervalStepToImage n i₂ ≫
        Y.stableIntervalImageToStable n h) := by
    rw [Y.stableIntervalStepToImage_comp_imageToStable n h]
    infer_instance
  let _ := hcomp
  exact epi_of_epi (Y.stableIntervalStepToImage n i₂)
    (Y.stableIntervalImageToStable n h)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₂∈ι, let δ:H^{n-1}_Y(i₂,⊤)→H^n_Y(⊥,i₂) be the connecting map for
⊥→i₂→⊤ and e_{i₂}:H^n_Y(⊥,i₂)→image(H^n_Y(⊥,i₂)→H^n_Y(⊥,⊤)) the image epimorphism. Then
δ≫e_{i₂}=0. The equality follows from the spectral zero relation after the monic image
inclusion. -/
@[reassoc]
theorem stableIntervalDelta_comp_toImage_zero
    (n : ℤ) (i₂ : ι) :
    Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) ≫
      Y.stableIntervalStepToImage n i₂ = 0  :=
  comp_factorThruImage_eq_zero
    (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
      (n - 1) n (by omega))
    (Y.stableIntervalStepToAbutment n i₂) (stableIntervalKernelZero Y n i₂)

/-- Let D be an abelian category, ι a preorder with bottom and top, and Y a spectral object in D
indexed by ι. For n∈ℤ and i₁≤i₂, let j:image u_{i₁}→image u_{i₂} be the ordered image inclusion
and q:image u_{i₂}→E_Y(⊥,i₁,i₂,⊤;n) the descended stable quotient. Then j≫q=0. This is the image
version of the vanishing composite of the preceding step with the stable quotient. -/
@[reassoc]
theorem stableIntervalImageMap_comp_imageToStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Y.stableIntervalImageToStable n h = 0 := by
  apply (cancel_epi (Y.stableIntervalStepToImage n i₁)).1
  rw [← Category.assoc,
    ← Y.stableIntervalStepToImage_naturality n h,
    Category.assoc,
    Y.stableIntervalStepToImage_comp_imageToStable n h,
    Y.stableIntervalStepMap_comp_toStable_zero n h,
    comp_zero]

noncomputable def stableIntervalOrderedImageCokernelIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel (Y.stableIntervalImageMap n h) ≅
      cokernel (imageCompMap (Y.stableIntervalStepMap n h)
        (Y.stableIntervalStepToAbutment n i₂)) :=
  cokernel.mapIso (Y.stableIntervalImageMap n h)
    (imageCompMap (Y.stableIntervalStepMap n h)
      (Y.stableIntervalStepToAbutment n i₂))
    (Limits.image.eqToIso (Y.stableIntervalStepMap_comp_toAbutment n h).symm)
    (Iso.refl _) (by
      apply (cancel_mono (Limits.image.ι (Y.stableIntervalStepToAbutment n i₂))).1
      simp only [Iso.refl_hom, Category.comp_id, Category.assoc]
      rw [Y.stableIntervalImageMap_comp_ι, imageCompMap_ι]
      exact Limits.image.eq_fac (Y.stableIntervalStepMap_comp_toAbutment n h).symm)

theorem cokernel_π_stableIntervalOrderedImageCokernelIso_inv
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (imageCompMap (Y.stableIntervalStepMap n h)
        (Y.stableIntervalStepToAbutment n i₂)) ≫
      (Y.stableIntervalOrderedImageCokernelIso n h).inv =
      cokernel.π (Y.stableIntervalImageMap n h) := by
  simp only [stableIntervalOrderedImageCokernelIso, cokernel.mapIso, cokernel.map,
    Iso.refl_inv, cokernel.π_desc, Category.id_comp]

/-- The stable spectral interval is the quotient of the two ordered abutment images.

Identify its native spectral cokernel with the quotient by the step and boundary maps,
apply `imageQuotientBiprodIso`, and transport the image-of-composite inclusion to the
specified ordered image inclusion. The boundary and exactness are the spectral laws. -/
noncomputable def stableIntervalImageCokernelIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅ cokernel (Y.stableIntervalImageMap n h) :=
  Y.stableIntervalStepCokernelIso n h ≪≫
    imageQuotientBiprodIso (Y.stableIntervalStepMap n h)
      (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega))
      (Y.stableIntervalStepToAbutment n i₂)
      (stableIntervalKernelZero Y n i₂) (stableIntervalKernelExact Y n i₂) ≪≫
    (Y.stableIntervalOrderedImageCokernelIso n h).symm

/-- The spectral comparison computes on the full image quotient projection. -/
@[reassoc]
theorem stableIntervalImageToStable_comp_iso_hom
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageToStable n h ≫ (Y.stableIntervalImageCokernelIso n h).hom =
      cokernel.π (Y.stableIntervalImageMap n h) := by
  apply (cancel_epi (Y.stableIntervalStepToImage n i₂)).1
  rw [← Category.assoc, Y.stableIntervalStepToImage_comp_imageToStable]
  change Y.stableIntervalStepToStable n h ≫
      (Y.stableIntervalStepCokernelIso n h).hom ≫
      imageQuotientForward (Y.stableIntervalStepMap n h)
        (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
          (n - 1) n (by omega))
        (Y.stableIntervalStepToAbutment n i₂) (stableIntervalKernelZero Y n i₂) ≫
      (Y.stableIntervalOrderedImageCokernelIso n h).inv = _
  rw [← Category.assoc, stableIntervalStepToStable_comp_stepCokernelIso Y,
    ← Category.assoc]
  change (cokernel.π (biprod.desc (Y.stableIntervalStepMap n h)
      (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega))) ≫
    imageQuotientForward (Y.stableIntervalStepMap n h)
      (Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega))
      (Y.stableIntervalStepToAbutment n i₂) (stableIntervalKernelZero Y n i₂)) ≫
    (Y.stableIntervalOrderedImageCokernelIso n h).inv =
      factorThruImage (Y.stableIntervalStepToAbutment n i₂) ≫
        cokernel.π (Y.stableIntervalImageMap n h)
  rw [cokernel_π_imageQuotientForward, Category.assoc,
    cokernel_π_stableIntervalOrderedImageCokernelIso_inv Y]

/-- The descended stable quotient is a cokernel of the ordered image inclusion.

Transport the standard categorical cokernel through the native quotient-of-images
comparison, using its specified projection law. -/
noncomputable def stableIntervalImageToStableIsCokernel
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    IsColimit (CokernelCofork.ofπ (Y.stableIntervalImageToStable n h)
      (Y.stableIntervalImageMap_comp_imageToStable_zero n h)) := by
  refine CokernelCofork.IsColimit.ofπ'
    (Y.stableIntervalImageToStable n h)
    (Y.stableIntervalImageMap_comp_imageToStable_zero n h) (fun {A} t ht => ?_)
  refine ⟨(Y.stableIntervalImageCokernelIso n h).hom ≫
    cokernel.desc (Y.stableIntervalImageMap n h) t ht, ?_⟩
  rw [← Category.assoc, Y.stableIntervalImageToStable_comp_iso_hom, cokernel.π_desc]

end CategoryTheory.Abelian.SpectralObject

end
