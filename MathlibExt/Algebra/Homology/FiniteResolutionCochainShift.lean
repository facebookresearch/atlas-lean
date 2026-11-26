/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolution
public import MathlibExt.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Finite resolutions as shifted bounded cochain complexes

Let P be preadditive with a zero object, A abelian and i : P → A additive. For a finite
resolution Q of X with support bound b, degree reversal n ↦ -n and zero extension give a cochain
complex supported in [-b,0]. The shift by -d places the original term Qₙ in degree d-n, with
support [d-b,d].

The differential keeps the shift factor (-1)^{-d}. The original augmentation gives
quasi-isomorphisms of the image complex to X concentrated in degree zero, or degree d after the
shift. Projectivity of the original image terms gives projectivity of every shifted image term.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P] [HasZeroObject P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] {X : A}

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. Reversing degree n to -n and
extending by zero gives an integer cochain complex with term Qₙ in degree -n. Its support is
contained in [-b,0]. -/
def cochainExtension (Q : FiniteResolution i X) : CochainComplex P ℤ :=
  Q.complex.extend ComplexShape.embeddingDownNat

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d ∈ ℤ, shifting the
extension by -d places Qₙ in degree d-n and the resolved object X in augmentation degree d. The
support is [d-b,d]. -/
def cochainShift (Q : FiniteResolution i X) (d : ℤ) : CochainComplex P ℤ :=
  Q.cochainExtension⟦-d⟧

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d ∈ ℤ and n ∈ ℕ, the degree
d-n term of the shifted cochain resolution is canonically isomorphic to Qₙ. -/
def cochainShiftTermIso (Q : FiniteResolution i X) (d : ℤ) (n : ℕ) :
    (Q.cochainShift d).X (d - (n : ℤ)) ≅ Q.complex.X n :=
  (Q.cochainExtension.shiftFunctorObjXIso (-d) (d - (n : ℤ)) (-(n : ℤ))
    (by omega)) ≪≫
    Q.complex.extendXIso ComplexShape.embeddingDownNat (by simp)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d,j,k ∈ ℤ, the differential
of the shifted cochain resolution is (-1)^{-d} times the extension differential from j-d to k-d,
retaining the standard shift sign. -/
theorem cochainShift_d (Q : FiniteResolution i X) (d j k : ℤ) :
    (Q.cochainShift d).d j k =
      (-d).negOnePow • Q.cochainExtension.d (j - d) (k - d) := by
  simp only [cochainShift, CochainComplex.shiftFunctor_obj_d']
  congr 1

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For every integer j<-b, the
degree-j term of the cochain extension is a zero object, because it corresponds to an original
chain term above b. -/
theorem cochainExtension_isZero_below (Q : FiniteResolution i X) (j : ℤ)
    (hj : j < -(Q.bound : ℤ)) : IsZero (Q.cochainExtension.X j) := by
  by_cases h : ∃ n : ℕ, -(n : ℤ) = j
  · obtain ⟨n, hn⟩ := h
    have hbound : Q.bound < n := by omega
    exact (Q.isZero_above n hbound).of_iso
      (Q.complex.extendXIso ComplexShape.embeddingDownNat (by simpa using hn))
  · exact Q.complex.isZero_extend_X ComplexShape.embeddingDownNat j (by
      intro n hn
      exact h ⟨n, by simpa using hn⟩)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. The cochain extension is zero in
every degree j>0, so its inclusive upper support bound is zero. -/
theorem cochainExtension_isStrictlyLE (Q : FiniteResolution i X) :
    CochainComplex.IsStrictlyLE Q.cochainExtension 0 := by
  unfold cochainExtension
  infer_instance

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. The cochain extension is zero in
every degree j<-b, so its inclusive lower support bound is -b. -/
theorem cochainExtension_isStrictlyGE (Q : FiniteResolution i X) :
    CochainComplex.IsStrictlyGE Q.cochainExtension (-(Q.bound : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro j hj
  exact Q.cochainExtension_isZero_below j hj

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For every d ∈ ℤ, the shifted
cochain resolution vanishes in degrees j>d; its inclusive upper support endpoint is d. -/
theorem cochainShift_isStrictlyLE (Q : FiniteResolution i X) (d : ℤ) :
    CochainComplex.IsStrictlyLE (Q.cochainShift d) d := by
  letI := Q.cochainExtension_isStrictlyLE
  exact CochainComplex.isStrictlyLE_shift Q.cochainExtension 0 (-d) d (by omega)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d ∈ ℤ, the shifted cochain
resolution vanishes in degrees j<d-b; its inclusive lower support endpoint is d-b. -/
theorem cochainShift_isStrictlyGE (Q : FiniteResolution i X) (d : ℤ) :
    CochainComplex.IsStrictlyGE (Q.cochainShift d) (d - (Q.bound : ℤ)) := by
  letI := Q.cochainExtension_isStrictlyGE
  exact CochainComplex.isStrictlyGE_shift Q.cochainExtension (-(Q.bound : ℤ))
    (-d) (d - (Q.bound : ℤ)) (by omega)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d,j ∈ ℤ with j>d, the
degree-j shifted term is a zero object. -/
theorem cochainShift_isZero_above (Q : FiniteResolution i X) (d j : ℤ) (hj : d < j) :
    IsZero ((Q.cochainShift d).X j) := by
  letI := Q.cochainShift_isStrictlyLE d
  exact CochainComplex.isZero_of_isStrictlyLE (Q.cochainShift d) d j hj

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d,j ∈ ℤ with j<d-b, the
degree-j shifted term is a zero object. -/
theorem cochainShift_isZero_below (Q : FiniteResolution i X) (d j : ℤ)
    (hj : j < d - (Q.bound : ℤ)) : IsZero ((Q.cochainShift d).X j) := by
  letI := Q.cochainShift_isStrictlyGE d
  exact CochainComplex.isZero_of_isStrictlyGE (Q.cochainShift d)
    (d - (Q.bound : ℤ)) j hj

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. The original augmentation, after
degree reversal and zero extension, gives a cochain map i(Q.cochainExtension) → X[0] in A. -/
def cochainExtensionAugmentation (Q : FiniteResolution i X) :
    (i.mapHomologicalComplex (.up ℤ)).obj Q.cochainExtension ⟶
      (CochainComplex.singleFunctor A 0).obj X :=
  (i.mapHomologicalComplexExtendIso ComplexShape.embeddingDownNat).inv.app Q.complex ≫
    HomologicalComplex.extendMap Q.augmentation ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X 0 0 (by simp)).hom

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. The augmentation
i(Q.cochainExtension) → X[0] is a quasi-isomorphism, as is the original finite-resolution
augmentation. -/
theorem cochainExtensionAugmentation_quasiIso (Q : FiniteResolution i X) :
    QuasiIso Q.cochainExtensionAugmentation := by
  let K0 : CochainComplex A ℤ := (i.mapHomologicalComplex (.up ℤ)).obj Q.cochainExtension
  let K1 : CochainComplex A ℤ := Q.mappedComplex.extend ComplexShape.embeddingDownNat
  let K2 : CochainComplex A ℤ :=
    ((ChainComplex.single₀ A).obj X).extend ComplexShape.embeddingDownNat
  let K3 : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj X
  let e0 : K1 ≅ K0 :=
    (i.mapHomologicalComplexExtendIso ComplexShape.embeddingDownNat).app Q.complex
  let f0 : K0 ⟶ K1 := e0.inv
  let f1 : K1 ⟶ K2 := HomologicalComplex.extendMap Q.augmentation ComplexShape.embeddingDownNat
  let f2 : K2 ⟶ K3 :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X 0 0 (by simp)).hom
  letI : IsIso f0 := by
    change IsIso e0.inv
    infer_instance
  letI : IsIso f2 := by
    dsimp only [f2]
    infer_instance
  have h0 : QuasiIso f0 := _root_.quasiIso_of_isIso f0
  have h1 : QuasiIso f1 :=
    (HomologicalComplex.quasiIso_extendMap_iff Q.augmentation
      ComplexShape.embeddingDownNat).2 Q.quasiIso
  have h2 : QuasiIso f2 := _root_.quasiIso_of_isIso f2
  have h12 : QuasiIso (f1 ≫ f2) :=
    _root_.quasiIso_comp f1 f2 (hφ := h1) (hφ' := h2)
  change QuasiIso (f0 ≫ (f1 ≫ f2))
  exact _root_.quasiIso_comp f0 (f1 ≫ f2) (hφ := h0) (hφ' := h12)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For d ∈ ℤ, the shifted
augmentation is i(Q.cochainShift d) → X[d], where X[d] here denotes the complex concentrated on
X in cochain degree d. -/
def cochainShiftAugmentation (Q : FiniteResolution i X) (d : ℤ) :
    (i.mapHomologicalComplex (.up ℤ)).obj (Q.cochainShift d) ⟶
      (CochainComplex.singleFunctor A d).obj X :=
  (i.mapCochainComplexShiftIso (-d)).hom.app Q.cochainExtension ≫
    (Q.cochainExtensionAugmentation⟦-d⟧') ≫
      ((CochainComplex.singleFunctors A).shiftIso (-d) d 0 (neg_add_cancel d)).hom.app X

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. For every integer d, the shifted
augmentation i(Q.cochainShift d) → the complex concentrated on X in degree d is a
quasi-isomorphism. -/
theorem cochainShiftAugmentation_quasiIso (Q : FiniteResolution i X) (d : ℤ) :
    QuasiIso (Q.cochainShiftAugmentation d) := by
  let K0 : CochainComplex A ℤ := (i.mapHomologicalComplex (.up ℤ)).obj (Q.cochainShift d)
  let K1 : CochainComplex A ℤ :=
    ((i.mapHomologicalComplex (.up ℤ)).obj Q.cochainExtension)⟦-d⟧
  let K2 : CochainComplex A ℤ := ((CochainComplex.singleFunctor A 0).obj X)⟦-d⟧
  let K3 : CochainComplex A ℤ := (CochainComplex.singleFunctor A d).obj X
  let e0 : K0 ≅ K1 := (i.mapCochainComplexShiftIso (-d)).app Q.cochainExtension
  let f0 : K0 ⟶ K1 := e0.hom
  let f1 : K1 ⟶ K2 := Q.cochainExtensionAugmentation⟦-d⟧'
  let f2 : K2 ⟶ K3 :=
    ((CochainComplex.singleFunctors A).shiftIso (-d) d 0 (neg_add_cancel d)).hom.app X
  letI : IsIso f0 := by
    change IsIso e0.hom
    infer_instance
  letI : IsIso f2 := by
    dsimp only [f2]
    infer_instance
  have h0 : QuasiIso f0 := _root_.quasiIso_of_isIso f0
  have h1 : QuasiIso f1 :=
    (CochainComplex.quasiIso_shift_iff Q.cochainExtensionAugmentation (-d)).2
      Q.cochainExtensionAugmentation_quasiIso
  have h2 : QuasiIso f2 := _root_.quasiIso_of_isIso f2
  have h12 : QuasiIso (f1 ≫ f2) :=
    _root_.quasiIso_comp f1 f2 (hφ := h1) (hφ' := h2)
  change QuasiIso (f0 ≫ (f1 ≫ f2))
  exact _root_.quasiIso_comp f0 (f1 ≫ f2) (hφ := h0) (hφ' := h12)

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. If every i(Qₙ) is projective in
A, then every i((Q.cochainShift d)ʲ) is projective for all d,j ∈ ℤ, including the zero terms
outside its support. -/
theorem cochainShift_projective_term (Q : FiniteResolution i X) (d j : ℤ)
    (hproj : ∀ n : ℕ, Projective (i.obj (Q.complex.X n))) :
    Projective (i.obj ((Q.cochainShift d).X j)) := by
  by_cases hj : j ≤ d
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = d - (n : ℤ) := by
      refine ⟨(d - j).toNat, ?_⟩
      omega
    subst j
    exact Projective.of_iso (i.mapIso (Q.cochainShiftTermIso d n)).symm (hproj n)
  · exact (i.map_isZero (Q.cochainShift_isZero_above d j (by omega))).projective

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. Under the two term
identifications at degrees d-(n+1) and d-n, the shifted differential is (-1)^{-d} times the
original chain differential Qₙ₊₁ → Qₙ. -/
theorem cochainShiftTermIso_d (Q : FiniteResolution i X) (d : ℤ) (n : ℕ) :
    (Q.cochainShiftTermIso d (n + 1)).inv ≫
        (Q.cochainShift d).d (d - ((n + 1 : ℕ) : ℤ)) (d - (n : ℤ)) ≫
          (Q.cochainShiftTermIso d n).hom =
      (-d).negOnePow • Q.complex.d (n + 1) n := by
  dsimp only [cochainShiftTermIso, cochainShift, cochainExtension]
  simp only [Iso.trans_inv, Iso.trans_hom,
    CochainComplex.shiftFunctor_obj_d', CochainComplex.shiftFunctorObjXIso,
    Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
    HomologicalComplex.XIsoOfEq_inv_comp_d_assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
  rw [Q.complex.extend_d_eq ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f (n + 1) = -((n + 1 : ℕ) : ℤ) by simp)
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by simp)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem cochainExtensionAugmentation_f_zero (Q : FiniteResolution i X) :
    Q.cochainExtensionAugmentation.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
      i.map (Q.complex.extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 0 = 0 by simp)).hom ≫ Q.augmentation₀ := by
  let K0 : CochainComplex A ℤ :=
    (i.mapHomologicalComplex (.up ℤ)).obj Q.cochainExtension
  let K1 : CochainComplex A ℤ := Q.mappedComplex.extend ComplexShape.embeddingDownNat
  let K2 : CochainComplex A ℤ :=
    ((ChainComplex.single₀ A).obj X).extend ComplexShape.embeddingDownNat
  let K3 : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj X
  let e : K1 ≅ K0 :=
    (i.mapHomologicalComplexExtendIso ComplexShape.embeddingDownNat).app Q.complex
  let f1 : K1 ⟶ K2 := HomologicalComplex.extendMap Q.augmentation ComplexShape.embeddingDownNat
  let f2 : K2 ⟶ K3 :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X 0 0 (by simp)).hom
  let t : Q.cochainExtension.X 0 ≅ Q.complex.X 0 :=
    Q.complex.extendXIso ComplexShape.embeddingDownNat (by simp)
  let t1 : K1.X 0 ≅ Q.mappedComplex.X 0 :=
    Q.mappedComplex.extendXIso ComplexShape.embeddingDownNat (by simp)
  let t2 : K2.X 0 ≅ ((ChainComplex.single₀ A).obj X).X 0 :=
    ((ChainComplex.single₀ A).obj X).extendXIso ComplexShape.embeddingDownNat (by simp)
  let s : K3.X 0 ≅ X := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  have hmap : e.hom.f 0 ≫ i.map t.hom = t1.hom :=
    i.mapHomologicalComplexExtendIso_hom_app_f ComplexShape.embeddingDownNat
      Q.complex 0 0 (by simp)
  have hinv : e.inv.f 0 ≫ t1.hom = i.map t.hom := by
    rw [← hmap, ← Category.assoc, ← HomologicalComplex.comp_f, e.inv_hom_id,
      HomologicalComplex.id_f, Category.id_comp]
  have h1 : f1.f 0 = t1.hom ≫ Q.augmentation.f 0 ≫ t2.inv :=
    HomologicalComplex.extendMap_f Q.augmentation ComplexShape.embeddingDownNat (by simp)
  have h2 : f2.f 0 = t2.hom ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).hom ≫ s.inv :=
    HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingDownNat X 0 0 (by simp)
  have hzero : Q.augmentation.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).hom = Q.augmentation₀ := by
    change Q.augmentation₀ ≫ 𝟙 X = Q.augmentation₀
    exact Category.comp_id _
  have hcomp : (e.inv ≫ (f1 ≫ f2)).f 0 = e.inv.f 0 ≫ f1.f 0 ≫ f2.f 0 :=
    (HomologicalComplex.comp_f e.inv (f1 ≫ f2) 0).trans
      (congrArg (fun f => e.inv.f 0 ≫ f) (HomologicalComplex.comp_f f1 f2 0))
  change (e.inv ≫ (f1 ≫ f2)).f 0 ≫ s.hom = i.map t.hom ≫ Q.augmentation₀
  calc
    _ = e.inv.f 0 ≫ f1.f 0 ≫ f2.f 0 ≫ s.hom := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ s.hom) hcomp
    _ = e.inv.f 0 ≫ t1.hom ≫ Q.augmentation₀ := by
      rw [h1, h2]
      simp only [Category.assoc, t2.inv_hom_id_assoc, s.inv_hom_id, Category.comp_id, hzero]
    _ = i.map t.hom ≫ Q.augmentation₀ := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ Q.augmentation₀) hinv

private theorem cochainShiftSingle_chart (d : ℤ) :
    (((CochainComplex.singleFunctors A).shiftIso (-d) d 0
      (neg_add_cancel d)).hom.app X).f d ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) d X).hom =
      (((CochainComplex.singleFunctor A 0).obj X).shiftFunctorObjXIso
        (-d) d 0 (by omega)).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom := by
  dsimp [CochainComplex.singleFunctors, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  simp only [eqToHom_trans]

/-- Let P be a preadditive category with a zero object, A an abelian category and i : P → A an
additive functor. Let Q be a finite resolution of X∈A by a nonnegative complex in P, with
augmentation i(Q) → X[0] and inclusive support bound b=Q.bound. In degree d, the augmentation
component, followed by the canonical identification of the concentrated target with X, is the
original augmentation Q₀ → X after i of the shifted degree-zero term identification. -/
theorem cochainShiftAugmentation_f (Q : FiniteResolution i X) (d : ℤ) :
    (Q.cochainShiftAugmentation d).f d ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) d X).hom =
      i.map ((Q.cochainShift d).XIsoOfEq
        (show d = d - (0 : ℤ) by simp)).hom ≫
          i.map (Q.cochainShiftTermIso d 0).hom ≫ Q.augmentation₀ := by
  let K : CochainComplex A ℤ :=
    (i.mapHomologicalComplex (.up ℤ)).obj Q.cochainExtension
  let S : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj X
  let K0 : CochainComplex A ℤ :=
    (i.mapHomologicalComplex (.up ℤ)).obj (Q.cochainShift d)
  let K1 : CochainComplex A ℤ := K⟦-d⟧
  let K2 : CochainComplex A ℤ := S⟦-d⟧
  let K3 : CochainComplex A ℤ := (CochainComplex.singleFunctor A d).obj X
  let e : K0 ≅ K1 := (i.mapCochainComplexShiftIso (-d)).app Q.cochainExtension
  let f1 : K1 ⟶ K2 := Q.cochainExtensionAugmentation⟦-d⟧'
  let f2 : K2 ⟶ K3 :=
    ((CochainComplex.singleFunctors A).shiftIso (-d) d 0 (neg_add_cancel d)).hom.app X
  let t : Q.cochainExtension.X 0 ≅ Q.complex.X 0 :=
    Q.complex.extendXIso ComplexShape.embeddingDownNat (by simp)
  let σ : (Q.cochainShift d).X d ≅ Q.cochainExtension.X 0 :=
    Q.cochainExtension.shiftFunctorObjXIso (-d) d 0 (by omega)
  let η : K1.X d ≅ K.X 0 := K.shiftFunctorObjXIso (-d) d 0 (by omega)
  let χ : K2.X d ≅ S.X 0 := S.shiftFunctorObjXIso (-d) d 0 (by omega)
  let s0 : S.X 0 ≅ X := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let sd : K3.X d ≅ X := HomologicalComplex.singleObjXSelf (.up ℤ) d X
  let z : (Q.cochainShift d).X d ≅ (Q.cochainShift d).X (d - (0 : ℤ)) :=
    (Q.cochainShift d).XIsoOfEq (by simp)
  let term : (Q.cochainShift d).X (d - (0 : ℤ)) ≅ Q.complex.X 0 :=
    Q.cochainShiftTermIso d 0
  have hshift : f1.f d = Q.cochainExtensionAugmentation.f (d + -d) :=
    CochainComplex.shiftFunctor_map_f' Q.cochainExtensionAugmentation (-d) d
  have hsingle : f2.f d ≫ sd.hom = χ.hom ≫ s0.hom := cochainShiftSingle_chart d
  have hnat : Q.cochainExtensionAugmentation.f (d + -d) ≫ χ.hom =
      η.hom ≫ Q.cochainExtensionAugmentation.f 0 :=
    HomologicalComplex.XIsoOfEq_hom_naturality Q.cochainExtensionAugmentation
      (show d + -d = 0 by omega)
  have hη : e.hom.f d ≫ η.hom = i.map σ.hom := by
    dsimp only [e, η, σ, K0, K1, K, cochainShift,
      Functor.mapCochainComplexShiftIso, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq, eqToIso.hom, Iso.app, NatIso.ofComponents,
      HomologicalComplex.Hom.isoOfComponents]
    simp only [Iso.refl_hom, eqToHom_map]
    exact Category.id_comp _
  have haug : Q.cochainExtensionAugmentation.f 0 ≫ s0.hom =
      i.map t.hom ≫ Q.augmentation₀ := cochainExtensionAugmentation_f_zero Q
  have hcomp : (e.hom ≫ (f1 ≫ f2)).f d = e.hom.f d ≫ f1.f d ≫ f2.f d :=
    (HomologicalComplex.comp_f e.hom (f1 ≫ f2) d).trans
      (congrArg (fun f => e.hom.f d ≫ f) (HomologicalComplex.comp_f f1 f2 d))
  have hactual : (Q.cochainShiftAugmentation d).f d ≫ sd.hom =
      i.map σ.hom ≫ i.map t.hom ≫ Q.augmentation₀ := by
    change (e.hom ≫ (f1 ≫ f2)).f d ≫ sd.hom =
      i.map σ.hom ≫ i.map t.hom ≫ Q.augmentation₀
    calc
      _ = e.hom.f d ≫ f1.f d ≫ f2.f d ≫ sd.hom := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ sd.hom) hcomp
      _ = e.hom.f d ≫ Q.cochainExtensionAugmentation.f (d + -d) ≫ χ.hom ≫ s0.hom := by
        rw [hshift, hsingle]
      _ = e.hom.f d ≫ η.hom ≫ Q.cochainExtensionAugmentation.f 0 ≫ s0.hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => e.hom.f d ≫ f ≫ s0.hom) hnat
      _ = i.map σ.hom ≫ Q.cochainExtensionAugmentation.f 0 ≫ s0.hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ Q.cochainExtensionAugmentation.f 0 ≫ s0.hom) hη
      _ = i.map σ.hom ≫ i.map t.hom ≫ Q.augmentation₀ :=
        congrArg (fun f => i.map σ.hom ≫ f) haug
  have hchart : ((Q.cochainShift d).XIsoOfEq
      (show d = d - (0 : ℤ) by simp)).hom ≫
        (Q.cochainShiftTermIso d 0).hom =
      (Q.cochainExtension.shiftFunctorObjXIso (-d) d 0 (by omega)).hom ≫
        (Q.complex.extendXIso ComplexShape.embeddingDownNat
          (show ComplexShape.embeddingDownNat.f 0 = 0 by simp)).hom := by
    dsimp only [cochainShiftTermIso, cochainShift, cochainExtension]
    rw [Iso.trans_hom, ← Category.assoc]
    congr 1
    simp only [CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToHom_trans]
  have hmapped : i.map z.hom ≫ i.map term.hom = i.map σ.hom ≫ i.map t.hom := calc
    _ = i.map (z.hom ≫ term.hom) := (i.map_comp z.hom term.hom).symm
    _ = i.map (σ.hom ≫ t.hom) := congrArg (fun f => i.map f) hchart
    _ = _ := i.map_comp σ.hom t.hom
  change (Q.cochainShiftAugmentation d).f d ≫ sd.hom =
    i.map z.hom ≫ i.map term.hom ≫ Q.augmentation₀
  calc
    _ = i.map σ.hom ≫ i.map t.hom ≫ Q.augmentation₀ := hactual
    _ = i.map z.hom ≫ i.map term.hom ≫ Q.augmentation₀ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ Q.augmentation₀) hmapped.symm

end CategoryTheory.Abelian.FiniteResolution

end
