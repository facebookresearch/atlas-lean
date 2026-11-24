/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition
public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleMonoCokernelComposition
public import MathlibExt.CategoryTheory.ExactCategory.ExtensionClosure
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Inherited exact structures on full subcategories of exact categories

A zero-containing, isomorphism-closed and extension-closed property in an
arbitrary exact category inherits precisely the original ambient
admissible rows. Genuine ambient kernel/cokernel composition and
pullback/pushout constructions prove the exact axioms. The original full
inclusion and independent object and morphism universes are retained.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe uH vH

namespace CategoryTheory.ExactCategory

variable {H : Type uH} [Category.{vH} H] [Preadditive H]
  [HasZeroObject H] [HasBinaryBiproducts H] [ExactCategory H]

/-- The inherited admissible rows are precisely the actual original
ambient admissible rows under the original full inclusion. -/
def inheritedAdmissible (Q : ObjectProperty H) (S : ShortComplex Q.FullSubcategory) : Prop :=
  ExactCategory.IsAdmissibleExact (S.map Q.ι)

namespace InheritedExact

variable (Q : ObjectProperty H) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]

/-- Full and faithful reflection of the actual original kernel row. -/
def kernel (S : ShortComplex Q.FullSubcategory) (hS : inheritedAdmissible Q S) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  apply isLimitOfReflects Q.ι
  exact (isLimitMapConeForkEquiv' Q.ι S.zero).symm
    (by simpa using ExactCategory.isLimit_kernelFork_of_isAdmissibleExact hS)

/-- Full and faithful reflection of the actual original cokernel row. -/
def cokernel (S : ShortComplex Q.FullSubcategory) (hS : inheritedAdmissible Q S) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  apply isColimitOfReflects Q.ι
  exact (isColimitMapCoconeCoforkEquiv' Q.ι S.zero).symm
    (by simpa using ExactCategory.isColimit_cokernelCofork_of_isAdmissibleExact hS)

omit [Q.IsClosedUnderIsomorphisms] in
/-- The reflected actual kernel/cokernel pair is internally short exact;
no abelian structure on the ambient category is used. -/
theorem shortExact (S : ShortComplex Q.FullSubcategory)
    (hS : inheritedAdmissible Q S) : S.ShortExact := by
  have hAmbient := ExactCategory.shortExact_of_isAdmissibleExact hS
  let _ : Mono S.f := Q.ι.mono_of_mono_map hAmbient.mono_f
  let _ : Epi S.g := Q.ι.epi_of_epi_map hAmbient.epi_g
  let hi := kernel Q S hS
  let hp := cokernel Q S hS
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 S.X₁ := by
    apply Fork.IsLimit.hom_ext hi
    change f' ≫ S.f = (𝟙 S.X₁) ≫ S.f
    have hFac : f' ≫ S.f = S.f :=
      Fork.IsLimit.lift_ι (t := KernelFork.ofι S.f S.zero) hi
    exact hFac.trans (Category.id_comp S.f).symm
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 S.X₃ := by
    apply Cofork.IsColimit.hom_ext hp
    change S.g ≫ g' = S.g ≫ (𝟙 S.X₃)
    have hFac : S.g ≫ g' = S.g :=
      Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ S.g S.zero) hp
    exact hFac.trans (Category.comp_id S.g).symm
  let hπ : IsColimit (CokernelCofork.ofπ (0 : S.X₁ ⟶ 0) (by simp : f' ≫ 0 = 0)) :=
    CokernelCofork.IsColimit.ofEpiOfIsZero _
      ((congrArg Epi hf').mpr (inferInstance : Epi (𝟙 S.X₁))) (isZero_zero _)
  let hι : IsLimit (KernelFork.ofι (0 : 0 ⟶ S.X₃) (by simp : 0 ≫ g' = 0)) :=
    KernelFork.IsLimit.ofMonoOfIsZero _
      ((congrArg Mono hg').mpr (inferInstance : Mono (𝟙 S.X₃))) (isZero_zero _)
  let data : S.HomologyData := {
    left := {
      K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := by simp
      hπ := hπ }
    right := {
      Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := by simp
      hι := hι }
    iso := Iso.refl 0
    comm := by simp [S.zero] }
  exact { exact := ⟨data, isZero_zero _⟩ }

variable (hExtension : ExtensionClosed Q)

include hExtension

omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
private theorem biprod_mem {X Y : H} (hX : Q X) (hY : Q Y) : Q (X ⊞ Y) :=
  (extensionClosed_iff Q).mp hExtension _ (ExactCategory.isAdmissibleExact_split X Y) hX hY

/-- Actual binary-product closure derived from the original extension input. -/
def binaryProducts : Q.IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⊞ Y :=
    HasLimit.isoOfNatIso (diagramIsoPair F) ≪≫ (biprod.isoProd X Y).symm
  exact Q.prop_of_iso e.symm (biprod_mem Q hExtension
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))

/-- Actual binary biproducts derived with the internally produced product closure. -/
def binaryBiproducts : HasBinaryBiproducts Q.FullSubcategory := by
  letI : Q.IsClosedUnderBinaryProducts := binaryProducts Q hExtension
  exact HasBinaryBiproducts.of_hasBinaryProducts

omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- The original inherited admissible epis compose, using the actual
extension of their original kernel objects. -/
theorem epiComposition :
    (CategoryTheory.admissibleEpisOf Q.FullSubcategory
      (inheritedAdmissible Q)).IsStableUnderComposition := by
  constructor
  intro X Y Z f g hf hg
  obtain ⟨Kf, ιf, wf, hF⟩ := hf
  obtain ⟨Kg, ιg, wg, hG⟩ := hg
  let F : ExactCategory.AdmissibleEpiKernelPresentation f.hom := {
    kernel := Kf.obj
    ι := ιf.hom
    zero := congrArg (fun k => k.hom) wf
    exact := hF }
  let G : ExactCategory.AdmissibleEpiKernelPresentation g.hom := {
    kernel := Kg.obj
    ι := ιg.hom
    zero := congrArg (fun k => k.hom) wg
    exact := hG }
  let C := F.composite G
  let row := ExactCategory.AdmissibleEpiKernelPresentation.compositeKernelSequence F G
  have hKernel : Q C.kernel := by
    have hRow := ExactCategory.AdmissibleEpiKernelPresentation.compositeKernelSequence_exact F G
    have hFirst : Q row.X₁ := by
      have hObject : row.X₁ = Kf.obj :=
        ExactCategory.AdmissibleEpiKernelPresentation.compositeKernelSequence_X₁ F G
      exact hObject.symm ▸ Kf.property
    have hThird : Q row.X₃ := by
      have hObject : row.X₃ = Kg.obj :=
        ExactCategory.AdmissibleEpiKernelPresentation.compositeKernelSequence_X₃ F G
      exact hObject.symm ▸ Kg.property
    have h := (extensionClosed_iff Q).mp hExtension row hRow hFirst hThird
    have hObject : row.X₂ = C.kernel :=
      ExactCategory.AdmissibleEpiKernelPresentation.compositeKernelSequence_X₂_eq_composite_kernel
        F G
    exact hObject ▸ h
  let K : Q.FullSubcategory := ⟨C.kernel, hKernel⟩
  let ι : K ⟶ X := ObjectProperty.homMk C.ι
  have w : ι ≫ (f ≫ g) = 0 := ObjectProperty.hom_ext _ C.zero
  exact ⟨K, ι, w, C.exact⟩

omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- The original inherited admissible monos compose, using the actual
extension of their two original quotient objects. -/
theorem monoComposition :
    (CategoryTheory.admissibleMonosOf Q.FullSubcategory
      (inheritedAdmissible Q)).IsStableUnderComposition := by
  constructor
  intro X Y Z f g hf hg
  obtain ⟨Cf, πf, wf, hF⟩ := hf
  obtain ⟨Cg, πg, wg, hG⟩ := hg
  let F : AdmissibleMonoCokernelPresentation f.hom := {
    cokernel := Cf.obj
    π := πf.hom
    zero := congrArg (fun k => k.hom) wf
    exact := hF }
  let G : AdmissibleMonoCokernelPresentation g.hom := {
    cokernel := Cg.obj
    π := πg.hom
    zero := congrArg (fun k => k.hom) wg
    exact := hG }
  let C := F.composite G
  let row := F.compositeCokernelSequence G
  have hQuotient : Q C.cokernel := by
    have hRow := F.compositeCokernelSequence_exact G
    have hFirst : Q row.X₁ := by
      have hObject : row.X₁ = Cf.obj := F.compositeCokernelSequence_X₁ G
      exact hObject.symm ▸ Cf.property
    have hThird : Q row.X₃ := by
      have hObject : row.X₃ = Cg.obj := F.compositeCokernelSequence_X₃ G
      exact hObject.symm ▸ Cg.property
    have h := (extensionClosed_iff Q).mp hExtension row hRow hFirst hThird
    have hObject : row.X₂ = C.cokernel := F.compositeCokernelSequence_X₂ G
    exact hObject ▸ h
  let W : Q.FullSubcategory := ⟨C.cokernel, hQuotient⟩
  let π : Z ⟶ W := ObjectProperty.homMk C.π
  have w : (f ≫ g) ≫ π = 0 := ObjectProperty.hom_ext _ C.zero
  exact ⟨W, π, w, C.exact⟩

omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- The actual ambient pullback of an inherited admissible epi lies
in the original full subcategory by its original kernel extension row. -/
theorem epiPullback {Y Z : Q.FullSubcategory} (p : Y ⟶ Z)
    (hp : CategoryTheory.admissibleEpisOf Q.FullSubcategory (inheritedAdmissible Q) p)
    (Z' : Q.FullSubcategory) (g : Z' ⟶ Z) :
    ∃ (P : Q.FullSubcategory) (fst : P ⟶ Z') (snd : P ⟶ Y),
      IsPullback fst snd g p ∧
        CategoryTheory.admissibleEpisOf Q.FullSubcategory (inheritedAdmissible Q) fst := by
  obtain ⟨K0, ι0, w0, h0⟩ := hp
  let K : ExactCategory.AdmissibleEpiKernelPresentation p.hom := {
    kernel := K0.obj
    ι := ι0.hom
    zero := congrArg (fun k => k.hom) w0
    exact := h0 }
  let E := K.baseChange g.hom
  let C := E.kernelPresentation
  have hFirst : Q C.kernel := by
    have hObject : C.kernel = K0.obj := E.kernelPresentation_kernel
    exact hObject.symm ▸ K0.property
  have hE : Q E.obj := (extensionClosed_iff Q).mp hExtension _ C.exact hFirst Z'.property
  let P : Q.FullSubcategory := ⟨E.obj, hE⟩
  let fst : P ⟶ Z' := ObjectProperty.homMk E.fst
  let snd : P ⟶ Y := ObjectProperty.homMk E.snd
  have hSquare : IsPullback fst snd g p :=
    IsPullback.of_map_of_faithful Q.ι E.square
  let first : Q.FullSubcategory := ⟨C.kernel, hFirst⟩
  let ι : first ⟶ P := ObjectProperty.homMk C.ι
  have w : ι ≫ fst = 0 := ObjectProperty.hom_ext _ C.zero
  exact ⟨P, fst, snd, hSquare, first, ι, w, C.exact⟩

omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- The actual ambient pushout of an inherited admissible mono lies
in the original full subcategory by its original quotient extension row. -/
theorem monoPushout {X Y : Q.FullSubcategory} (i : X ⟶ Y)
    (hi : CategoryTheory.admissibleMonosOf Q.FullSubcategory (inheritedAdmissible Q) i)
    (X' : Q.FullSubcategory) (f : X ⟶ X') :
    ∃ (P : Q.FullSubcategory) (inl : X' ⟶ P) (inr : Y ⟶ P),
      IsPushout f i inl inr ∧
        CategoryTheory.admissibleMonosOf Q.FullSubcategory (inheritedAdmissible Q) inl := by
  obtain ⟨C0, π0, w0, h0⟩ := hi
  let C : AdmissibleMonoCokernelPresentation i.hom := {
    cokernel := C0.obj
    π := π0.hom
    zero := congrArg (fun k => k.hom) w0
    exact := h0 }
  obtain ⟨E⟩ := C.cobaseChange_nonempty f.hom
  let D := C.cobaseChangePresentation E
  have hThird : Q D.cokernel := by
    have hObject : D.cokernel = C0.obj := C.cobaseChangePresentation_cokernel E
    exact hObject.symm ▸ C0.property
  have hE : Q E.obj := (extensionClosed_iff Q).mp hExtension _ D.exact X'.property hThird
  let P : Q.FullSubcategory := ⟨E.obj, hE⟩
  let inl : X' ⟶ P := ObjectProperty.homMk E.inl
  let inr : Y ⟶ P := ObjectProperty.homMk E.inr
  have hSquare : IsPushout f i inl inr :=
    IsPushout.of_map_of_faithful Q.ι E.square
  let third : Q.FullSubcategory := ⟨D.cokernel, hThird⟩
  let π : P ⟶ third := ObjectProperty.homMk D.π
  have w : inl ≫ π = 0 := ObjectProperty.hom_ext _ D.zero
  exact ⟨P, inl, inr, hSquare, third, π, w, D.exact⟩

/-- The named inherited exact structure has precisely the original
ambient admissible rows under the actual full-subcategory inclusion. -/
@[instance_reducible]
def exactCategory :
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts Q hExtension
    ExactCategory Q.FullSubcategory := by
  letI : Q.IsClosedUnderBinaryProducts := binaryProducts Q hExtension
  letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts Q hExtension
  exact {
    IsAdmissibleExact := inheritedAdmissible Q
    shortExact_of_isAdmissibleExact := fun {S} hS => shortExact Q S hS
    isLimit_kernelFork := fun {S} hS => ⟨kernel Q S hS⟩
    isColimit_cokernelCofork := fun {S} hS => ⟨cokernel Q S hS⟩
    isAdmissibleExact_of_iso := by
      intro S T e hS
      exact ExactCategory.isAdmissibleExact_of_iso (Q.ι.mapShortComplex.mapIso e) hS
    isAdmissibleExact_split X Y :=
      ExactCategory.isAdmissibleExact_of_splitting
        ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map Q.ι)
    admissibleMono_comp := monoComposition Q hExtension
    admissibleEpi_comp := epiComposition Q hExtension
    admissibleMono_pushout := fun _ _ i hi X' f => monoPushout Q hExtension i hi X' f
    admissibleEpi_pullback := fun _ _ p hp Z' g => epiPullback Q hExtension p hp Z' g }

/-- The genuine full inclusion is exact for the internally constructed
exact structure, with no caller exact-functor certificate. -/
theorem inclusion_exact :
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts Q hExtension
    letI : ExactCategory Q.FullSubcategory := exactCategory Q hExtension
    Q.ι.IsExact :=
  letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts Q hExtension
  letI : ExactCategory Q.FullSubcategory := exactCategory Q hExtension
  { map_admissibleExact := fun _ hS => hS }

/-- The inherited structure's admissibility has its actual original
whole-row value under the full inclusion. -/
theorem admissible_iff (S : ShortComplex Q.FullSubcategory) :
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts Q hExtension
    letI : ExactCategory Q.FullSubcategory := exactCategory Q hExtension
    ExactCategory.IsAdmissibleExact S ↔ ExactCategory.IsAdmissibleExact (S.map Q.ι) :=
  Iff.rfl

end InheritedExact

/-- Internally produced exact-structure data for the actual original
full subcategory. It is derived from the original closure hypotheses. -/
structure ExactFullSubcategoryData (Q : ObjectProperty H) where
  containsZero : Q.ContainsZero
  isoClosed : Q.IsClosedUnderIsomorphisms
  binaryBiproducts : HasBinaryBiproducts Q.FullSubcategory
  /-- The internally derived original ambient-row exact structure on the full subcategory. -/
  exactStructure :
    letI : Q.ContainsZero := containsZero
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts
    ExactCategory Q.FullSubcategory
  inclusionExact :
    letI : Q.ContainsZero := containsZero
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts
    letI : ExactCategory Q.FullSubcategory := exactStructure
    Q.ι.IsExact
  admissible :
    letI : Q.ContainsZero := containsZero
    letI : HasBinaryBiproducts Q.FullSubcategory := binaryBiproducts
    letI : ExactCategory Q.FullSubcategory := exactStructure
    ∀ S : ShortComplex Q.FullSubcategory,
      ExactCategory.IsAdmissibleExact S ↔ ExactCategory.IsAdmissibleExact (S.map Q.ι)

/-- The original general inherited exact data is constructed internally
from its genuine zero/iso/extension closure; no exact-structure outcome is
caller input. The original full inclusion is retained. -/
def extensionClosedExactData (Q : ObjectProperty H) [Q.ContainsZero]
    [Q.IsClosedUnderIsomorphisms] (hExtension : ExtensionClosed Q) :
    ExactFullSubcategoryData Q := by
  letI : Q.IsClosedUnderBinaryProducts := InheritedExact.binaryProducts Q hExtension
  letI : HasBinaryBiproducts Q.FullSubcategory := HasBinaryBiproducts.of_hasBinaryProducts
  exact {
    containsZero := inferInstance
    isoClosed := inferInstance
    binaryBiproducts := inferInstance
    exactStructure := InheritedExact.exactCategory Q hExtension
    inclusionExact := InheritedExact.inclusion_exact Q hExtension
    admissible := InheritedExact.admissible_iff Q hExtension }

end CategoryTheory.ExactCategory

end
