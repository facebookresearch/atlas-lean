/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTopKernel
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import MathlibExt.Algebra.Homology.HomotopyCofiberQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Single

/-!
# Ambient-acyclic truncation at an explicit original support window

The supplied integers and geometric support proof remain fixed.
The returned original kernel has upper endpoint `b - 1`.
The disk is the original homotopy cofiber of the identity on the stock top
single complex. The projection uses the stock mapping-cone lift of the
degree-zero term projection and its negative cochain boundary. Its actual
lower component is the original top differential with the positive sign;
its upper component is the original top identity through the same term chart.

The source kernel and its support are earned pointwise from the original
admissible epimorphisms. No source homology or global source kernels are inputs.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CochainComplex.HomComplex
open scoped ZeroObject

namespace CochainComplex.Bounded.TruncationAt

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

variable (b : ℤ)

omit [HasZeroObject E] [HasBinaryBiproducts E] in
/-- An empty original support window makes the unchanged original raw complex zero. -/
theorem isZero_of_empty_window (K : Bounded E) (a : ℤ)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (hEmpty : b < a) :
    IsZero K.obj := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext j
  exact (hSupport j (by omega)).eq_of_tgt _ _

/-- The same stock single complex on the actual top term of the original bounded cochain. -/
abbrev topDiskSingle (K : Bounded E) : CochainComplex E ℤ :=
  (HomologicalComplex.single E (.up ℤ) (b)).obj (K.obj.X (b))

/-- The actual identity homotopy cofiber of the stock original top single complex. -/
abbrev topDiskRaw (K : Bounded E) : CochainComplex E ℤ :=
  HomologicalComplex.homotopyCofiber (𝟙 (topDiskSingle (b := b) K))

/-- Only the two original top degrees can be nonzero in the actual disk. -/
theorem topDisk_isZero_X (K : Bounded E) (j : ℤ)
    (hLower : j ≠ b - 1) (hUpper : j ≠ b) :
    IsZero ((topDiskRaw (b := b) K).X j) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X (𝟙 (topDiskSingle (b := b) K)) j
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
      (K.obj.X (b)) j hUpper
  · intro k hk
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
      (K.obj.X (b)) k (by change j + 1 = k at hk; omega)

/-- The lower term uses the actual left summand and original single-term chart. -/
def topDiskLowerIso (K : Bounded E) :
    K.obj.X (b) ≅ (topDiskRaw (b := b) K).X (b - 1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
    (K.obj.X (b))).symm ≪≫
      isoBiprodZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
        (K.obj.X (b)) (b - 1) (by omega)) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (topDiskSingle (b := b) K))
        (b - 1) (b)
        (ComplexShape.up_mk _ _ (by omega))).symm

/-- The upper term uses the actual right summand and the same original single-term chart. -/
def topDiskUpperIso (K : Bounded E) :
    K.obj.X (b) ≅ (topDiskRaw (b := b) K).X (b) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
    (K.obj.X (b))).symm ≪≫
      isoZeroBiprod (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
        (K.obj.X (b)) (b + 1) (by omega)) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (topDiskSingle (b := b) K))
        (b) (b + 1) (ComplexShape.up_mk _ _ rfl)).symm

/-- The canonical lower chart is the original cofiber left inclusion. -/
theorem topDiskLowerIso_hom (K : Bounded E) :
    (topDiskLowerIso (b := b) K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
        (b) (b - 1)
        (ComplexShape.up_mk _ _ (by omega)) := rfl

/-- The canonical upper chart is the original cofiber right inclusion. -/
theorem topDiskUpperIso_hom (K : Bounded E) :
    (topDiskUpperIso (b := b) K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) (b) := by
  exact congrArg
    (fun f => (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
      (K.obj.X (b))).inv ≫ f)
    (HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv (𝟙 (topDiskSingle (b := b) K))
      (b + 1) (b) (ComplexShape.up_mk _ _ rfl))

/-- The actual signed cofiber differential gives the positive identity between the two charts. -/
theorem topDiskLowerIso_hom_d (K : Bounded E) :
    (topDiskLowerIso (b := b) K).hom ≫ (topDiskRaw (b := b) K).d (b - 1) (b) =
      (topDiskUpperIso (b := b) K).hom := by
  have hd := HomologicalComplex.homotopyCofiber.inlX_d (𝟙 (topDiskSingle (b := b) K))
    (b - 1) (b) (b + 1)
    (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)
  have hpos : HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
      (b) (b - 1) (ComplexShape.up_mk _ _ (by omega)) ≫
      (topDiskRaw (b := b) K).d (b - 1) (b) =
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) (b) := by
    change HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
      (b) (b - 1) (ComplexShape.up_mk _ _ (by omega)) ≫
      HomologicalComplex.homotopyCofiber.d (𝟙 (topDiskSingle (b := b) K))
        (b - 1) (b) = _
    simpa only [topDiskSingle, HomologicalComplex.single_obj_d, neg_zero, zero_comp,
      HomologicalComplex.id_f, Category.id_comp, zero_add] using hd
  rw [topDiskLowerIso_hom (b := b), topDiskUpperIso_hom (b := b), Category.assoc]
  exact congrArg (fun f =>
    (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
      (K.obj.X (b))).inv ≫ f) hpos

/-- The original degree-zero cochain is the identity on the actual top term. -/
def topDiskCochain (K : Bounded E) : Cochain K.obj (topDiskSingle (b := b) K) 0 :=
  Cochain.ofHoms (fun j => if h : j = b then
    eqToHom (congrArg K.obj.X h) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      eqToHom (congrArg (topDiskSingle (b := b) K).X h.symm) else 0)

/-- Its negative cochain boundary supplies the stock cone lift's first coordinate. -/
def topDiskBoundary (K : Bounded E) : Cocycle K.obj (topDiskSingle (b := b) K) 1 :=
  Cocycle.mk (-δ 0 1 (topDiskCochain (b := b) K)) 2 rfl (by simp only [δ_neg, δ_δ, neg_zero])

/-- The actual whole projection is the stock mapping-cone lift of these original cochains. -/
def topDiskProjection (K : Bounded E) : K.obj ⟶ topDiskRaw (b := b) K :=
  mappingCone.lift (𝟙 (topDiskSingle (b := b) K)) (topDiskBoundary (b := b) K) (topDiskCochain (b
    := b) K) (by
    simp only [topDiskBoundary, Cocycle.mk, Cochain.comp_id]
    exact add_neg_cancel _)

omit [HasBinaryBiproducts E] in
/-- At the original top degree the cochain uses the same stock single-term inverse. -/
theorem topDiskCochain_self (K : Bounded E) :
    (topDiskCochain (b := b) K).v (b) (b) (add_zero _) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv := by
  simp only [topDiskCochain, Cochain.ofHoms_v, dite_eq_left rfl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

omit [HasBinaryBiproducts E] in
/-- Every other original degree-zero cochain component vanishes. -/
theorem topDiskCochain_ne (K : Bounded E) (j : ℤ) (hj : j ≠ b) :
    (topDiskCochain (b := b) K).v j j (add_zero _) = 0 := by
  simp only [topDiskCochain, Cochain.ofHoms_v, dite_eq_right hj]

omit [HasBinaryBiproducts E] in
/-- The boundary coordinate has the positive original differential sign. -/
theorem topDiskBoundary_v (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskBoundary (b := b) K).1.v p q hpq =
      K.obj.d p q ≫ (topDiskCochain (b := b) K).v q q (add_zero _) := by
  change (-δ 0 1 (topDiskCochain (b := b) K)).v p q hpq = _
  rw [Cochain.neg_v, δ_v 0 1 rfl (topDiskCochain (b := b) K) p q hpq p q (by omega) hpq]
  simp only [topDiskSingle, HomologicalComplex.single_obj_d, comp_zero,
    Int.negOnePow_one, Units.neg_smul, one_smul, zero_add, neg_neg]

/-- The whole original cone projection keeps both actual coordinate summands. -/
theorem topDiskProjection_f (K : Bounded E) (j : ℤ) :
    (topDiskProjection (b := b) K).f j =
      (topDiskBoundary (b := b) K).1.v j (j + 1) rfl ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K)) (j + 1) j rfl +
        (topDiskCochain (b := b) K).v j j (add_zero j) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) j :=
  mappingCone.lift_f _ _ _ _ j (j + 1) rfl

/-- The stock projection formula at any specified original adjacent degrees. -/
theorem topDiskProjection_f' (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskProjection (b := b) K).f p =
      (topDiskBoundary (b := b) K).1.v p q hpq ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K)) q p
            (ComplexShape.up_mk _ _ hpq) +
        (topDiskCochain (b := b) K).v p p (add_zero p) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) p :=
  mappingCone.lift_f _ _ _ _ p q hpq

/-- The upper projection component is the actual original identity through the disk chart. -/
theorem topDiskProjection_f_upper (K : Bounded E) :
    (topDiskProjection (b := b) K).f (b) = (topDiskUpperIso (b := b) K).hom := by
  rw [topDiskProjection_f' (b := b) K (b) (b + 1) rfl,
    topDiskBoundary_v (b := b), topDiskCochain_ne (b := b) K (b + 1) (by omega),
    comp_zero, zero_comp, zero_add, topDiskCochain_self (b := b)]
  exact (topDiskUpperIso_hom (b := b) K).symm

/-- The lower projection component is the unchanged positive original top differential. -/
theorem topDiskProjection_f_lower (K : Bounded E) :
    (topDiskProjection (b := b) K).f (b - 1) =
      K.obj.d (b - 1) (b) ≫ (topDiskLowerIso (b := b) K).hom := by
  rw [topDiskProjection_f' (b := b) K (b - 1) (b) (by omega),
    topDiskBoundary_v (b := b), topDiskCochain_self (b := b),
    topDiskCochain_ne (b := b) K (b - 1) (by omega), zero_comp, add_zero,
    topDiskLowerIso_hom (b := b), Category.assoc]

/-- The original upper projection component is an isomorphism. -/
theorem topDiskProjection_isIso_upper (K : Bounded E) :
    IsIso ((topDiskProjection (b := b) K).f (b)) := by
  rw [topDiskProjection_f_upper (b := b)]
  infer_instance

/-- The actual stock disk has its original support window `[b−1,b]`. -/
theorem bounded_topDiskRaw (K : Bounded E) : CochainComplex.bounded E (topDiskRaw (b := b) K) := by
  refine ⟨b - 1, b, ?_⟩
  intro j hj
  exact topDisk_isZero_X (b := b) K j (by omega) (by omega)

/-- Reify the same actual stock identity cofiber in the original bounded category. -/
def topDisk (K : Bounded E) : Bounded E := ⟨topDiskRaw (b := b) K, bounded_topDiskRaw (b := b) K⟩

/-- The entire bounded projection is the same original raw disk projection. -/
def topDiskProjectionBounded (K : Bounded E) : K ⟶ topDisk (b := b) K :=
  ObjectProperty.homMk (topDiskProjection (b := b) K)

/-- The original whole disk projection survives the native bounded lift. -/
theorem topDiskProjectionBounded_hom (K : Bounded E) :
    (topDiskProjectionBounded (b := b) K).hom = topDiskProjection (b := b) K := rfl

/-- The same actual identity cofiber is contracted by the stock cone homotopy constructor. -/
def topDiskContraction (K : Bounded E) :
    _root_.Homotopy (𝟙 (topDiskRaw (b := b) K)) 0 := by
  change _root_.Homotopy (𝟙 (mappingCone (𝟙 (topDiskSingle (b := b) K)))) 0
  exact mappingCone.descHomotopy (𝟙 (topDiskSingle (b := b) K))
    (𝟙 (mappingCone (𝟙 (topDiskSingle (b := b) K)))) 0
    0 (mappingCone.inl (𝟙 (topDiskSingle (b := b) K))) (by simp) (by simp)

/-- The actual stock disk is acyclic after any additive ambient functor. -/
theorem topDisk_map_acyclic {A : Type uA} [Category.{vA} A] [Abelian A]
    (F : E ⥤ A) [F.Additive] (K : Bounded E) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw (b := b) K)).Acyclic := by
  let M := (F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw (b := b) K)
  have hContract : _root_.Homotopy (𝟙 M) 0 := by
    have hid : (F.mapHomologicalComplex (.up ℤ)).map (𝟙 (topDiskRaw (b := b) K)) = 𝟙 M :=
      (F.mapHomologicalComplex (.up ℤ)).map_id _
    have hz : (F.mapHomologicalComplex (.up ℤ)).map (0 : topDiskRaw (b := b) K ⟶ topDiskRaw (b :=
      b) K) = 0 :=
      (F.mapHomologicalComplex (.up ℤ)).map_zero _ _
    have h := F.mapHomotopy (topDiskContraction (b := b) K)
    rw [hid, hz] at h
    exact h
  intro j
  apply (M.exactAt_iff_isZero_homology j).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
    using hContract.homologyMap_eq j

variable [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

variable (a : ℤ)

/-- Every actual original disk-projection component is an admissible source epimorphism. -/
theorem topDiskProjection_isAdmissibleEpi (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleEpi ((topDiskProjection (b := b) K).f j) := by
  by_cases hUpper : j = b
  · subst j
    let _ := topDiskProjection_isIso_upper (b := b) K
    exact isAdmissibleEpi_of_isIso _
  by_cases hLower : j = b - 1
  · subst j
    rw [topDiskProjection_f_lower (b := b)]
    let _ : Epi (F.map (K.obj.d (b - 1) b)) :=
      mappedDifferential_epi_of_acyclic_of_isZero_succ F K b
        (hSupport (b + 1) (Or.inr (by omega))) hK
    have hAdmissible : IsAdmissibleEpi (K.obj.d (b - 1) b) :=
      isAdmissibleEpi_g (F.kernelLiftOfEpi_isAdmissibleExact hKernelClosure (K.obj.d (b - 1) b))
    exact admissibleEpi_comp.comp_mem _ _ hAdmissible
      (isAdmissibleEpi_of_isIso (topDiskLowerIso (b := b) K).hom)
  let e := (topDisk_isZero_X (b := b) K j hLower hUpper).iso (isZero_zero E)
  have hComp : IsAdmissibleEpi
      (((topDiskProjection (b := b) K).f j ≫ e.hom) ≫ e.inv) :=
    admissibleEpi_comp.comp_mem _ _ (IsAdmissibleEpi.toZero _)
      (isAdmissibleEpi_of_isIso e.inv)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hComp

/-- Each source kernel is earned from the actual component admissible epimorphism. -/
theorem topDiskProjection_hasKernel_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    HasKernel ((topDiskProjection (b := b) K).f j) := by
  obtain ⟨Z, i, w, hS⟩ := topDiskProjection_isAdmissibleEpi (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK j
  exact ⟨⟨⟨KernelFork.ofι i w, isLimit_kernelFork_of_isAdmissibleExact hS⟩⟩⟩

/-- The stock pointwise construction earns the actual raw kernel of the original projection. -/
theorem topDiskProjection_hasKernel (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HasKernel (topDiskProjection (b := b) K) := by
  let _ : ∀ j, HasKernel ((topDiskProjection (b := b) K).f j) :=
    topDiskProjection_hasKernel_f (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
  exact HomologicalComplex.hasKernel_of_hasKernel_f _

/-- The actual chosen raw kernel, formed with the earned pointwise source kernels. -/
def topTruncationRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel (topDiskProjection (b := b) K)

/-- The actual raw kernel inclusion into the unchanged original complex. -/
def topTruncationRawι (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ K.obj := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel.ι (topDiskProjection (b := b) K)

/-- The entire original raw kernel/projection face is zero. -/
theorem topTruncationRawι_projection (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ≫
      topDiskProjection (b := b) K = 0 := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel.condition _

/-- The actual stock raw kernel has its original kernel universal property. -/
def topTruncationKernelIsLimit (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := topDiskProjection (b := b) K)
      (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)
      (topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK)) := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernelIsKernel _

/-- Evaluation preserves this actual kernel using the earned individual component kernels. -/
def topTruncationTermIsLimit (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsLimit (KernelFork.ofι (f := (topDiskProjection (b := b) K).f j)
      ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).f j) (by
        exact congrArg (fun t => t.f j) (topTruncationRawι_projection (b := b) (a := a) (hSupport
          := hSupport) F hKernelClosure K hK))) := by
  let _ : ∀ n, HasKernel ((topDiskProjection (b := b) K).f n) :=
    topDiskProjection_hasKernel_f (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
  let _ := HomologicalComplex.eval_preservesLimit_of_hasKernel_f (topDiskProjection (b := b) K) j
  exact KernelFork.mapIsLimit _ (topTruncationKernelIsLimit (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK)
    (HomologicalComplex.eval E (.up ℤ) j)

/-- The actual kernel term is zero whenever its original containing term is zero. -/
theorem topTruncationRaw_isZero_X_of_isZero (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ)
    (hj : IsZero (K.obj.X j)) :
    IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X j)
      := by
  let _ : Mono ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK).f j) :=
    Fork.IsLimit.mono (topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK j)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).f j)).mp
  simp only [Category.id_comp, zero_comp]
  exact hj.eq_of_tgt _ _

/-- The upper term of the actual kernel vanishes because its original projection is an iso. -/
theorem topTruncationRaw_isZero_X_upper (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X
      (b)) := by
  let _ := topDiskProjection_isIso_upper (b := b) K
  exact KernelFork.IsLimit.isZero_of_mono
    (topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK (b))

/-- The actual kernel retains the original lower support and loses precisely the top term. -/
theorem topTruncationRaw_support (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ∀ j : ℤ, j < a ∨ b - 1 < j →
      IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X
        j) := by
  intro j hj
  rcases hj with hLower | hUpper
  · exact topTruncationRaw_isZero_X_of_isZero (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK j
      (hSupport j (Or.inl hLower))
  · by_cases hTop : j = b
    · subst j
      exact topTruncationRaw_isZero_X_upper (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK
    · exact topTruncationRaw_isZero_X_of_isZero (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK j
        (hSupport j (Or.inr (by omega)))

/-- The same actual raw kernel is bounded with the earned original truncation window. -/
theorem bounded_topTruncationRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK) :=
  ⟨a, b - 1, topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK⟩

/-- Reify the same actual stock raw kernel in the original bounded carrier. -/
def topTruncation (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  ⟨topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK,
    bounded_topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK⟩

/-- The entire bounded kernel inclusion is the same original raw kernel inclusion. -/
def topTruncationι (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ K :=
  ObjectProperty.homMk (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

/-- The original whole kernel inclusion is retained by the bounded lift. -/
theorem topTruncationι_hom (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom =
      topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK := rfl

/-- The same complete original kernel/projection face is zero in the bounded category. -/
theorem topTruncationι_projection (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ≫
      topDiskProjectionBounded (b := b) K = 0 := by
  apply (fullyFaithfulι E).map_injective
  exact topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK

/-- The actual original raw kernel and projection form the same original short complex. -/
abbrev topTruncationRawShortComplex (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ShortComplex (CochainComplex E ℤ) :=
  ShortComplex.mk (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK) (topDiskProjection (b := b) K)
    (topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

/-- Every actual source kernel row is the original admissible short sequence. -/
theorem topTruncationRawShortComplex_term_isAdmissibleExact (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleExact ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK).map
      (HomologicalComplex.eval E (.up ℤ) j)) := by
  obtain ⟨Z, i, w, hS⟩ := topDiskProjection_isAdmissibleEpi (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK j
  let hKernel := isLimit_kernelFork_of_isAdmissibleExact hS
  let hActual := topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK j
  let e := hKernel.conePointUniqueUpToIso hActual
  have he := IsLimit.conePointUniqueUpToIso_hom_comp hKernel hActual WalkingParallelPair.zero
  have he' : e.hom ≫ (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).f j = i := he
  let eS : ShortComplex.mk i ((topDiskProjection (b := b) K).f j) w ≅
      (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).map
        (HomologicalComplex.eval E (.up ℤ) j) :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by
      change e.hom ≫ (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
        K hK).f j = i ≫ 𝟙 _
      rw [Category.comp_id]
      exact he') (by
      change 𝟙 _ ≫ (topDiskProjection (b := b) K).f j = (topDiskProjection (b := b) K).f j ≫ 𝟙 _
      simp)
  exact isAdmissibleExact_of_iso eS hS

/-- The same actual bounded inclusion is admissible on every original source component. -/
theorem topTruncationι_isAdmissibleMono_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleMono ((topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).hom.f j) :=
  isAdmissibleMono_f
    (topTruncationRawShortComplex_term_isAdmissibleExact (b := b) (a := a) (hSupport := hSupport)
      F hKernelClosure K hK j)

variable [F.IsExact]

/-- The specified exact embedding maps the actual original raw kernel row to a short exact row. -/
theorem topTruncationRawShortComplex_map_shortExact (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).map
      (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  change (((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).map
    (HomologicalComplex.eval E (.up ℤ) j)).map F).ShortExact
  exact F.map_admissibleExact _
    (topTruncationRawShortComplex_term_isAdmissibleExact (b := b) (a := a) (hSupport := hSupport)
      F hKernelClosure K hK j)

/-- The actual good top truncation stays acyclic in the same specified ambient weak model. -/
theorem topTruncation_map_acyclic (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).obj).Acyclic
        := by
  let S := (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).map
    (F.mapHomologicalComplex (.up ℤ))
  have hS : S.ShortExact := topTruncationRawShortComplex_map_shortExact (b := b) (a := a)
    (hSupport := hSupport) F hKernelClosure K hK
  intro j
  have hExact := hS.homology_exact₁ (j - 1) j (ComplexShape.up_mk _ _ (by omega))
  have hPrev : IsZero (S.X₃.homology (j - 1)) :=
    (topDisk_map_acyclic (b := b) F K (j - 1)).isZero_homology
  have hNext : IsZero (S.X₂.homology j) := (hK j).isZero_homology
  have hZero := hExact.isZero_X₂ (hPrev.eq_of_src _ _) (hNext.eq_of_tgt _ _)
  exact (S.X₁.exactAt_iff_isZero_homology j).mpr hZero

/-- The same original signed homotopy cofiber of the actual raw truncation inclusion. -/
abbrev topTruncationCofiberRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  HomologicalComplex.homotopyCofiber (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

omit [F.IsExact] in
/-- The actual cofiber uses the original lower support shifted once and the original upper bound. -/
theorem bounded_topTruncationCofiberRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK) := by
  refine ⟨a - 1, b, ?_⟩
  intro j hj
  apply HomologicalComplex.homotopyCofiber.isZero_X (topTruncationRawι (b := b) (a := a) (hSupport
    := hSupport) F hKernelClosure K hK) j
  · have hBound := hSupport j
    change (j < a ∨ b < j) → IsZero (K.obj.X j) at hBound
    exact hBound (by omega)
  · intro n hn
    change j + 1 = n at hn
    exact topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
      n (by omega)

/-- Reify the same original signed cofiber in the original bounded category. -/
def topTruncationCofiber (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  ⟨topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK,
    bounded_topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK⟩

/-- The raw descendant is exactly the stock original cofiber descendant of the earned raw row. -/
abbrev topTruncationCofiberDescRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶
      topDiskRaw (b := b) K :=
  HomologicalComplex.homotopyCofiber.descShortComplex
    (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

omit [F.IsExact] in
/-- The complete original old-complex face equals the original whole disk projection. -/
theorem topTruncationCofiber_inr_desc (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HomologicalComplex.homotopyCofiber.inr (topTruncationRawι (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) ≫
      topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK =
        topDiskProjection (b := b) K := by
  exact HomologicalComplex.homotopyCofiber.inr_descShortComplex
    (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

omit [F.IsExact] in
/-- The full shifted-source component face is the actual zero homotopy of the original raw row. -/
theorem topTruncationCofiber_inlX_desc_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (topTruncationRawι (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) j i hij ≫
      (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).f i = 0 := by
  let S := topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK
  change HomologicalComplex.homotopyCofiber.inlX S.f j i hij ≫
    (HomologicalComplex.homotopyCofiber.descShortComplex S).f i = 0
  rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
    HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp]

/-- The same complete original cofiber descendant is retained in the native bounded carrier. -/
def topTruncationCofiberDesc (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiber (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ topDisk
      (b := b) K :=
  ObjectProperty.homMk (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

omit [F.IsExact] in
/-- The bounded descendant retains the same entire original raw map. -/
theorem topTruncationCofiberDesc_hom (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberDesc (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom =
      topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
        := rfl

/-- The earned ambient cofiber chart is the same stock additive-functor comparison. -/
abbrev topTruncationCofiberMapIso (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (F.mapHomologicalComplex (.up ℤ)).obj (topTruncationCofiberRaw (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (topTruncationRawι (b := b) (a := a) (hSupport :=
          hSupport) F hKernelClosure K hK)) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso
    (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK) F

omit [F.IsExact] in
/-- Both original cofiber faces earn the whole ambient descendant equality under the actual chart.
-/
theorem topTruncationCofiberDesc_map (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberMapIso (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
          hK).map
          (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (topTruncationCofiberDescRaw (b := b) (a := a)
        (hSupport := hSupport) F hKernelClosure K hK) := by
  let S := topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK
  let J := F.mapHomologicalComplex (.up ℤ)
  let e : J.obj (HomologicalComplex.homotopyCofiber S.f) ≅
      HomologicalComplex.homotopyCofiber (S.map J).f :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso S.f F
  have he (j : ℤ) : e.inv.f j =
      (HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjXIso S.f F j).inv := rfl
  have hInv : e.inv ≫ J.map (HomologicalComplex.homotopyCofiber.descShortComplex S) =
      HomologicalComplex.homotopyCofiber.descShortComplex (S.map J) := by
    ext j
    change e.inv.f j ≫ F.map ((HomologicalComplex.homotopyCofiber.descShortComplex S).f j) =
      (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
    rw [he]
    apply HomologicalComplex.homotopyCofiber.ext_from_X (J.map S.f) (j + 1) j
      (ComplexShape.up_mk _ _ rfl)
    · rw [HomologicalComplex.homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv_assoc,
        ← F.map_comp, HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp, F.map_zero]
      change 0 = HomologicalComplex.homotopyCofiber.inlX (S.map J).f (j + 1) j
        (ComplexShape.up_mk _ _ rfl) ≫
        (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
      rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp]
    · rw [HomologicalComplex.homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc,
        ← F.map_comp, HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
      change (S.map J).g.f j = HomologicalComplex.homotopyCofiber.inrX (S.map J).f j ≫
        (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
      rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
  change e.hom ≫ HomologicalComplex.homotopyCofiber.descShortComplex (S.map J) =
    J.map (HomologicalComplex.homotopyCofiber.descShortComplex S)
  apply (cancel_epi e.inv).mp
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact hInv.symm

/-- The same actual original cofiber descendant is a weak equivalence in the ambient model. -/
theorem topTruncationCofiberDesc_map_quasiIso (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (topTruncationCofiberDesc (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).hom) := by
  change QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
    (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK))
  rw [← topTruncationCofiberDesc_map (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK]
  exact quasiIso_comp
    (hφ := (inferInstance : QuasiIso (topTruncationCofiberMapIso (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK).hom))
    (hφ' := HomologicalComplex.homotopyCofiber.quasiIso_descShortComplex_up _
      (topTruncationRawShortComplex_map_shortExact (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK))
    (topTruncationCofiberMapIso (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom
    (HomologicalComplex.homotopyCofiber.descShortComplex
      ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).map
        (F.mapHomologicalComplex (.up ℤ))))

omit [F.IsExact] in
/-- The same actual returned kernel has the original lower bound and a strictly smaller upper
  bound. -/
theorem topTruncation_strict_support (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    b - 1 < b ∧ ∀ j : ℤ, j < a ∨ b - 1 < j →
      IsZero ((topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).obj.X
        j) :=
  ⟨by omega, topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK⟩

end CochainComplex.Bounded.TruncationAt

end
