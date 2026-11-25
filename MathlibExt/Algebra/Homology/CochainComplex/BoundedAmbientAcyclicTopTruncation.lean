/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTruncationAt

/-!
# The actual top disk and kernel truncation of an ambient-acyclic bounded cochain

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

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

/-- The same stock single complex on the actual top term of the original bounded cochain. -/
abbrev topDiskSingle (K : Bounded E) : CochainComplex E ℤ :=
  TruncationAt.topDiskSingle (b := topCutoff K) (K := K)

/-- The actual identity homotopy cofiber of the stock original top single complex. -/
abbrev topDiskRaw (K : Bounded E) : CochainComplex E ℤ :=
  TruncationAt.topDiskRaw (b := topCutoff K) (K := K)

/-- Only the two original top degrees can be nonzero in the actual disk. -/
theorem topDisk_isZero_X (K : Bounded E) (j : ℤ)
    (hLower : j ≠ topCutoff K - 1) (hUpper : j ≠ topCutoff K) :
    IsZero ((topDiskRaw K).X j) :=
  TruncationAt.topDisk_isZero_X (b := topCutoff K) (K := K) (j := j) (hLower := hLower) (hUpper :=
    hUpper)

/-- The lower term uses the actual left summand and original single-term chart. -/
abbrev topDiskLowerIso (K : Bounded E) :
    K.obj.X (topCutoff K) ≅ (topDiskRaw K).X (topCutoff K - 1) :=
  TruncationAt.topDiskLowerIso (b := topCutoff K) (K := K)

/-- The upper term uses the actual right summand and the same original single-term chart. -/
abbrev topDiskUpperIso (K : Bounded E) :
    K.obj.X (topCutoff K) ≅ (topDiskRaw K).X (topCutoff K) :=
  TruncationAt.topDiskUpperIso (b := topCutoff K) (K := K)

/-- The canonical lower chart is the original cofiber left inclusion. -/
theorem topDiskLowerIso_hom (K : Bounded E) :
    (topDiskLowerIso K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv ≫
      HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K))
        (topCutoff K) (topCutoff K - 1)
        (ComplexShape.up_mk _ _ (by omega)) :=
  TruncationAt.topDiskLowerIso_hom (b := topCutoff K) (K := K)

/-- The canonical upper chart is the original cofiber right inclusion. -/
theorem topDiskUpperIso_hom (K : Bounded E) :
    (topDiskUpperIso K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv ≫
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) (topCutoff K) :=
  TruncationAt.topDiskUpperIso_hom (b := topCutoff K) (K := K)

/-- The actual signed cofiber differential gives the positive identity between the two charts. -/
theorem topDiskLowerIso_hom_d (K : Bounded E) :
    (topDiskLowerIso K).hom ≫ (topDiskRaw K).d (topCutoff K - 1) (topCutoff K) =
      (topDiskUpperIso K).hom :=
  TruncationAt.topDiskLowerIso_hom_d (b := topCutoff K) (K := K)

/-- The original degree-zero cochain is the identity on the actual top term. -/
abbrev topDiskCochain (K : Bounded E) : Cochain K.obj (topDiskSingle K) 0 :=
  TruncationAt.topDiskCochain (b := topCutoff K) (K := K)

/-- Its negative cochain boundary supplies the stock cone lift's first coordinate. -/
abbrev topDiskBoundary (K : Bounded E) : Cocycle K.obj (topDiskSingle K) 1 :=
  TruncationAt.topDiskBoundary (b := topCutoff K) (K := K)

/-- The actual whole projection is the stock mapping-cone lift of these original cochains. -/
abbrev topDiskProjection (K : Bounded E) : K.obj ⟶ topDiskRaw K :=
  TruncationAt.topDiskProjection (b := topCutoff K) (K := K)

omit [HasBinaryBiproducts E] in
/-- At the original top degree the cochain uses the same stock single-term inverse. -/
theorem topDiskCochain_self (K : Bounded E) :
    (topDiskCochain K).v (topCutoff K) (topCutoff K) (add_zero _) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv :=
  TruncationAt.topDiskCochain_self (b := topCutoff K) (K := K)

omit [HasBinaryBiproducts E] in
/-- Every other original degree-zero cochain component vanishes. -/
theorem topDiskCochain_ne (K : Bounded E) (j : ℤ) (hj : j ≠ topCutoff K) :
    (topDiskCochain K).v j j (add_zero _) = 0 :=
  TruncationAt.topDiskCochain_ne (b := topCutoff K) (K := K) (j := j) (hj := hj)

omit [HasBinaryBiproducts E] in
/-- The boundary coordinate has the positive original differential sign. -/
theorem topDiskBoundary_v (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskBoundary K).1.v p q hpq =
      K.obj.d p q ≫ (topDiskCochain K).v q q (add_zero _) :=
  TruncationAt.topDiskBoundary_v (b := topCutoff K) (K := K) (p := p) (q := q) (hpq := hpq)

/-- The whole original cone projection keeps both actual coordinate summands. -/
theorem topDiskProjection_f (K : Bounded E) (j : ℤ) :
    (topDiskProjection K).f j =
      (topDiskBoundary K).1.v j (j + 1) rfl ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K)) (j + 1) j rfl +
        (topDiskCochain K).v j j (add_zero j) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) j :=
  TruncationAt.topDiskProjection_f (b := topCutoff K) (K := K) (j := j)

/-- The stock projection formula at any specified original adjacent degrees. -/
theorem topDiskProjection_f' (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskProjection K).f p =
      (topDiskBoundary K).1.v p q hpq ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K)) q p
            (ComplexShape.up_mk _ _ hpq) +
        (topDiskCochain K).v p p (add_zero p) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) p :=
  TruncationAt.topDiskProjection_f' (b := topCutoff K) (K := K) (p := p) (q := q) (hpq := hpq)

/-- The upper projection component is the actual original identity through the disk chart. -/
theorem topDiskProjection_f_upper (K : Bounded E) :
    (topDiskProjection K).f (topCutoff K) = (topDiskUpperIso K).hom :=
  TruncationAt.topDiskProjection_f_upper (b := topCutoff K) (K := K)

/-- The lower projection component is the unchanged positive original top differential. -/
theorem topDiskProjection_f_lower (K : Bounded E) :
    (topDiskProjection K).f (topCutoff K - 1) =
      K.obj.d (topCutoff K - 1) (topCutoff K) ≫ (topDiskLowerIso K).hom :=
  TruncationAt.topDiskProjection_f_lower (b := topCutoff K) (K := K)

/-- The original upper projection component is an isomorphism. -/
theorem topDiskProjection_isIso_upper (K : Bounded E) :
    IsIso ((topDiskProjection K).f (topCutoff K)) :=
  TruncationAt.topDiskProjection_isIso_upper (b := topCutoff K) (K := K)

/-- The actual stock disk has its original support window `[b−1,b]`. -/
theorem bounded_topDiskRaw (K : Bounded E) : CochainComplex.bounded E (topDiskRaw K) :=
  TruncationAt.bounded_topDiskRaw (b := topCutoff K) (K := K)

/-- Reify the same actual stock identity cofiber in the original bounded category. -/
abbrev topDisk (K : Bounded E) : Bounded E :=
  TruncationAt.topDisk (b := topCutoff K) (K := K)

/-- The entire bounded projection is the same original raw disk projection. -/
abbrev topDiskProjectionBounded (K : Bounded E) : K ⟶ topDisk K :=
  TruncationAt.topDiskProjectionBounded (b := topCutoff K) (K := K)

/-- The original whole disk projection survives the native bounded lift. -/
theorem topDiskProjectionBounded_hom (K : Bounded E) :
    (topDiskProjectionBounded K).hom = topDiskProjection K :=
  TruncationAt.topDiskProjectionBounded_hom (b := topCutoff K) (K := K)

/-- The same actual identity cofiber is contracted by the stock cone homotopy constructor. -/
abbrev topDiskContraction (K : Bounded E) :
    _root_.Homotopy (𝟙 (topDiskRaw K)) 0 :=
  TruncationAt.topDiskContraction (b := topCutoff K) (K := K)

/-- The actual stock disk is acyclic after any additive ambient functor. -/
theorem topDisk_map_acyclic {A : Type uA} [Category.{vA} A] [Abelian A]
    (F : E ⥤ A) [F.Additive] (K : Bounded E) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw K)).Acyclic :=
  TruncationAt.topDisk_map_acyclic (b := topCutoff K) (F := F) (K := K)

variable [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

/-- Every actual original disk-projection component is an admissible source epimorphism. -/
theorem topDiskProjection_isAdmissibleEpi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleEpi ((topDiskProjection K).f j) :=
  TruncationAt.topDiskProjection_isAdmissibleEpi (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- Each source kernel is earned from the actual component admissible epimorphism. -/
theorem topDiskProjection_hasKernel_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    HasKernel ((topDiskProjection K).f j) :=
  TruncationAt.topDiskProjection_hasKernel_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- The stock pointwise construction earns the actual raw kernel of the original projection. -/
theorem topDiskProjection_hasKernel (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HasKernel (topDiskProjection K) :=
  TruncationAt.topDiskProjection_hasKernel (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The actual chosen raw kernel, formed with the earned pointwise source kernels. -/
abbrev topTruncationRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  TruncationAt.topTruncationRaw (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a
    := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The actual raw kernel inclusion into the unchanged original complex. -/
abbrev topTruncationRawι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRaw F hKernelClosure K hK ⟶ K.obj :=
  TruncationAt.topTruncationRawι (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a
    := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The entire original raw kernel/projection face is zero. -/
theorem topTruncationRawι_projection (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRawι F hKernelClosure K hK ≫ topDiskProjection K = 0 :=
  TruncationAt.topTruncationRawι_projection (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The actual stock raw kernel has its original kernel universal property. -/
abbrev topTruncationKernelIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := topDiskProjection K)
      (topTruncationRawι F hKernelClosure K hK)
      (topTruncationRawι_projection F hKernelClosure K hK)) :=
  TruncationAt.topTruncationKernelIsLimit (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Evaluation preserves this actual kernel using the earned individual component kernels. -/
abbrev topTruncationTermIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsLimit (KernelFork.ofι (f := (topDiskProjection K).f j)
      ((topTruncationRawι F hKernelClosure K hK).f j) (by
        exact congrArg (fun t => t.f j) (topTruncationRawι_projection F hKernelClosure K hK))) :=
  TruncationAt.topTruncationTermIsLimit (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- The actual kernel term is zero whenever its original containing term is zero. -/
theorem topTruncationRaw_isZero_X_of_isZero (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ)
    (hj : IsZero (K.obj.X j)) :
    IsZero ((topTruncationRaw F hKernelClosure K hK).X j) :=
  TruncationAt.topTruncationRaw_isZero_X_of_isZero (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j) (hj := hj)

/-- The upper term of the actual kernel vanishes because its original projection is an iso. -/
theorem topTruncationRaw_isZero_X_upper (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsZero ((topTruncationRaw F hKernelClosure K hK).X (topCutoff K)) :=
  TruncationAt.topTruncationRaw_isZero_X_upper (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The actual kernel retains the original lower support and loses precisely the top term. -/
theorem topTruncationRaw_support (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ∀ j : ℤ, j < K.property.choose ∨ topCutoff K - 1 < j →
      IsZero ((topTruncationRaw F hKernelClosure K hK).X j) :=
  TruncationAt.topTruncationRaw_support (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The same actual raw kernel is bounded with the earned original truncation window. -/
theorem bounded_topTruncationRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationRaw F hKernelClosure K hK) :=
  TruncationAt.bounded_topTruncationRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Reify the same actual stock raw kernel in the original bounded carrier. -/
abbrev topTruncation (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  TruncationAt.topTruncation (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a :=
    K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The entire bounded kernel inclusion is the same original raw kernel inclusion. -/
abbrev topTruncationι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncation F hKernelClosure K hK ⟶ K :=
  TruncationAt.topTruncationι (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a :=
    K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The original whole kernel inclusion is retained by the bounded lift. -/
theorem topTruncationι_hom (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationι F hKernelClosure K hK).hom = topTruncationRawι F hKernelClosure K hK :=
  TruncationAt.topTruncationι_hom (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure)
    (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The same complete original kernel/projection face is zero in the bounded category. -/
theorem topTruncationι_projection (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationι F hKernelClosure K hK ≫ topDiskProjectionBounded K = 0 :=
  TruncationAt.topTruncationι_projection (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The actual original raw kernel and projection form the same original short complex. -/
abbrev topTruncationRawShortComplex (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ShortComplex (CochainComplex E ℤ) :=
  TruncationAt.topTruncationRawShortComplex (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Every actual source kernel row is the original admissible short sequence. -/
theorem topTruncationRawShortComplex_term_isAdmissibleExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleExact ((topTruncationRawShortComplex F hKernelClosure K hK).map
      (HomologicalComplex.eval E (.up ℤ) j)) :=
  TruncationAt.topTruncationRawShortComplex_term_isAdmissibleExact (b := topCutoff K) (F := F)
    (hKernelClosure := hKernelClosure) (a := K.property.choose) (hSupport :=
    K.property.choose_spec.choose_spec) (K := K) (hK := hK) (j := j)

/-- The same actual bounded inclusion is admissible on every original source component. -/
theorem topTruncationι_isAdmissibleMono_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleMono ((topTruncationι F hKernelClosure K hK).hom.f j) :=
  TruncationAt.topTruncationι_isAdmissibleMono_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

variable [F.IsExact]

/-- The specified exact embedding maps the actual original raw kernel row to a short exact row. -/
theorem topTruncationRawShortComplex_map_shortExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topTruncationRawShortComplex F hKernelClosure K hK).map
      (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  TruncationAt.topTruncationRawShortComplex_map_shortExact (b := topCutoff K) (F := F)
    (hKernelClosure := hKernelClosure) (a := K.property.choose) (hSupport :=
    K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The actual good top truncation stays acyclic in the same specified ambient weak model. -/
theorem topTruncation_map_acyclic (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (topTruncation F hKernelClosure K hK).obj).Acyclic :=
  TruncationAt.topTruncation_map_acyclic (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The same original signed homotopy cofiber of the actual raw truncation inclusion. -/
abbrev topTruncationCofiberRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  TruncationAt.topTruncationCofiberRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- The actual cofiber uses the original lower support shifted once and the original upper bound. -/
theorem bounded_topTruncationCofiberRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationCofiberRaw F hKernelClosure K hK) :=
  TruncationAt.bounded_topTruncationCofiberRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Reify the same original signed cofiber in the original bounded category. -/
abbrev topTruncationCofiber (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  TruncationAt.topTruncationCofiber (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure)
    (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- The raw descendant is exactly the stock original cofiber descendant of the earned raw row. -/
abbrev topTruncationCofiberDescRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiberRaw F hKernelClosure K hK ⟶ topDiskRaw K :=
  TruncationAt.topTruncationCofiberDescRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- The complete original old-complex face equals the original whole disk projection. -/
theorem topTruncationCofiber_inr_desc (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HomologicalComplex.homotopyCofiber.inr (topTruncationRawι F hKernelClosure K hK) ≫
      topTruncationCofiberDescRaw F hKernelClosure K hK = topDiskProjection K :=
  TruncationAt.topTruncationCofiber_inr_desc (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- The full shifted-source component face is the actual zero homotopy of the original raw row. -/
theorem topTruncationCofiber_inlX_desc_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (topTruncationRawι F hKernelClosure K hK) j i hij ≫
      (topTruncationCofiberDescRaw F hKernelClosure K hK).f i = 0 :=
  TruncationAt.topTruncationCofiber_inlX_desc_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (i := i) (j := j) (hij := hij)

/-- The same complete original cofiber descendant is retained in the native bounded carrier. -/
abbrev topTruncationCofiberDesc (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiber F hKernelClosure K hK ⟶ topDisk K :=
  TruncationAt.topTruncationCofiberDesc (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- The bounded descendant retains the same entire original raw map. -/
theorem topTruncationCofiberDesc_hom (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberDesc F hKernelClosure K hK).hom =
      topTruncationCofiberDescRaw F hKernelClosure K hK :=
  TruncationAt.topTruncationCofiberDesc_hom (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The earned ambient cofiber chart is the same stock additive-functor comparison. -/
abbrev topTruncationCofiberMapIso (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (F.mapHomologicalComplex (.up ℤ)).obj (topTruncationCofiberRaw F hKernelClosure K hK) ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (topTruncationRawι F hKernelClosure K hK)) :=
  TruncationAt.topTruncationCofiberMapIso (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Both original cofiber faces earn the whole ambient descendant equality under the actual chart.
-/
theorem topTruncationCofiberDesc_map (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberMapIso F hKernelClosure K hK).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((topTruncationRawShortComplex F hKernelClosure K hK).map
          (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (topTruncationCofiberDescRaw F hKernelClosure K hK) :=
  TruncationAt.topTruncationCofiberDesc_map (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- The same actual original cofiber descendant is a weak equivalence in the ambient model. -/
theorem topTruncationCofiberDesc_map_quasiIso (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (topTruncationCofiberDesc F hKernelClosure K hK).hom) :=
  TruncationAt.topTruncationCofiberDesc_map_quasiIso (b := topCutoff K) (F := F) (hKernelClosure
    := hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec)
    (K := K) (hK := hK)

end CochainComplex.Bounded

end
