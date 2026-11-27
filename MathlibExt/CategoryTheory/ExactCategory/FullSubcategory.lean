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

public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exact structures on extension-closed full subcategories

An isomorphism-stable full subcategory of an abelian category that contains
zero and is closed under extensions inherits its actual short exact rows.
The construction uses ambient kernels, cokernels, pullbacks and pushouts.
Its exact structure is a named value, since exact structures are data.

The ambient object and morphism universes remain independent. The closure
conditions are stock `ObjectProperty` properties; no replacement category
or additional exact-category certificate is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  [P.ContainsZero] [P.IsClosedUnderExtensions]

/-- Binary products of an extension-closed full subcategory are inherited
from the ambient binary biproducts. -/
instance (priority := 100) ObjectProperty.binaryProducts_of_extensions :
    P.IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⊞ Y :=
    HasLimit.isoOfNatIso (diagramIsoPair F) ≪≫ (biprod.isoProd X Y).symm
  exact P.prop_of_iso e.symm (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))

/-- The full subcategory has its actual binary biproducts. -/
instance (priority := 100) ObjectProperty.binaryBiproducts_of_extensions :
    HasBinaryBiproducts P.FullSubcategory :=
  HasBinaryBiproducts.of_hasBinaryProducts

namespace ExactCategory

/-- Admissibility inherited from the ambient abelian category is actual
ambient short exactness under the full inclusion. -/
def fullSubcategoryAdmissible (S : ShortComplex P.FullSubcategory) : Prop :=
  (S.map P.ι).ShortExact

/-- The kernel universal property of an actual ambient short exact row
reflects through the full subcategory inclusion. -/
def fullSubcategoryKernel (S : ShortComplex P.FullSubcategory)
    (hS : fullSubcategoryAdmissible P S) : IsLimit (KernelFork.ofι S.f S.zero) := by
  apply isLimitOfReflects P.ι
  exact (isLimitMapConeForkEquiv' P.ι S.zero).symm (by simpa using hS.fIsKernel)

/-- The cokernel universal property of an actual ambient short exact row
reflects through the full subcategory inclusion. -/
def fullSubcategoryCokernel (S : ShortComplex P.FullSubcategory)
    (hS : fullSubcategoryAdmissible P S) : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  apply isColimitOfReflects P.ι
  exact (isColimitMapCoconeCoforkEquiv' P.ι S.zero).symm (by simpa using hS.gIsCokernel)

omit [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] in
/-- An ambient short exact row is internally short exact in the full
subcategory, using its actual reflected kernel and cokernel pair. -/
theorem fullSubcategoryShortExact (S : ShortComplex P.FullSubcategory)
    (hS : fullSubcategoryAdmissible P S) : S.ShortExact := by
  let _ : Mono S.f := P.ι.mono_of_mono_map hS.mono_f
  let _ : Epi S.g := P.ι.epi_of_epi_map hS.epi_g
  let hi := fullSubcategoryKernel P S hS
  let hp := fullSubcategoryCokernel P S hS
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 S.X₁ := by
    apply hi.hom_ext
    intro j
    cases j <;> simp [f']
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 S.X₃ := by
    apply hp.hom_ext
    intro j
    cases j <;> simp [g']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) :=
    CokernelCofork.IsColimit.ofEpiOfIsZero _
      ((congrArg Epi hf').mpr (inferInstance : Epi (𝟙 S.X₁))) (isZero_zero _)
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) :=
    KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; infer_instance) (isZero_zero _)
  let h : S.HomologyData :=
    { left := { K := S.X₁, H := 0, i := S.f, wi := S.zero, hi := hi,
                π := 0, wπ := wπ, hπ := hπ }
      right := { Q := S.X₃, H := 0, p := S.g, wp := S.zero, hp := hp,
                 ι := 0, wι := wι, hι := hι }
      iso := Iso.refl 0
      comm := by simp [S.zero] }
  exact { exact := ⟨h, isZero_zero _⟩ }

omit [P.ContainsZero] [P.IsClosedUnderExtensions] in
/-- Inherited admissible monomorphisms have actual ambient monomorphisms
and an ambient cokernel in the object property. -/
theorem fullSubcategoryMono_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    admissibleMonosOf P.FullSubcategory (fullSubcategoryAdmissible P) f ↔
      Mono f.hom ∧ P (cokernel f.hom) := by
  constructor
  · rintro ⟨Z, g, w, hS⟩
    change (ShortComplex.mk f.hom g.hom _).ShortExact at hS
    let e := hS.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel f.hom)
    exact ⟨hS.mono_f, P.prop_of_iso e Z.property⟩
  · rintro ⟨hf, hQ⟩
    let _ : Mono f.hom := hf
    let Q : P.FullSubcategory := ⟨cokernel f.hom, hQ⟩
    let g : Y ⟶ Q := ObjectProperty.homMk (cokernel.π f.hom)
    have w : f ≫ g = 0 := ObjectProperty.hom_ext _ (cokernel.condition f.hom)
    refine ⟨Q, g, w, ?_⟩
    change (ShortComplex.mk f.hom (cokernel.π f.hom) _).ShortExact
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f.hom)
      inferInstance inferInstance

omit [P.ContainsZero] [P.IsClosedUnderExtensions] in
/-- Inherited admissible epimorphisms have actual ambient epimorphisms
and an ambient kernel in the object property. -/
theorem fullSubcategoryEpi_iff {Y Z : P.FullSubcategory} (g : Y ⟶ Z) :
    admissibleEpisOf P.FullSubcategory (fullSubcategoryAdmissible P) g ↔
      Epi g.hom ∧ P (kernel g.hom) := by
  constructor
  · rintro ⟨X, f, w, hS⟩
    change (ShortComplex.mk f.hom g.hom _).ShortExact at hS
    let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel g.hom)
    exact ⟨hS.epi_g, P.prop_of_iso e X.property⟩
  · rintro ⟨hg, hK⟩
    let _ : Epi g.hom := hg
    let K : P.FullSubcategory := ⟨kernel g.hom, hK⟩
    let f : K ⟶ Y := ObjectProperty.homMk (kernel.ι g.hom)
    have w : f ≫ g = 0 := ObjectProperty.hom_ext _ (kernel.condition g.hom)
    refine ⟨K, f, w, ?_⟩
    change (ShortComplex.mk (kernel.ι g.hom) g.hom _).ShortExact
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel g.hom)
      inferInstance inferInstance

omit [P.IsClosedUnderIsomorphisms] [P.ContainsZero] in
/-- If the second map is mono, the composite cokernel is an extension
of the two actual cokernels. -/
theorem cokernel_comp_mem {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono g] (hf : P (cokernel f)) (hg : P (cokernel g)) :
    P (cokernel (f ≫ g)) := by
  let E := kernelCokernelCompSequence_exact f g
  let S := E.sc 3
  let T := E.sc 2
  have hT : T.Exact := E.exact 2
  have hzero : T.f = 0 := (isZero_kernel_of_mono g).eq_of_src _ _
  let _ : Mono S.f := (T.exact_iff_mono hzero).mp hT
  let _ : Epi S.g := inferInstance
  have hS : S.ShortExact := { exact := E.exact 3 (by decide) }
  exact P.prop_X₂_of_shortExact hS hf hg

omit [P.IsClosedUnderIsomorphisms] [P.ContainsZero] in
/-- If the first map is epi, the composite kernel is an extension
of the two actual kernels. -/
theorem kernel_comp_mem {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Epi f] (hf : P (kernel f)) (hg : P (kernel g)) :
    P (kernel (f ≫ g)) := by
  let E := kernelCokernelCompSequence_exact f g
  let S := E.sc 0
  let T := E.sc 1
  have hT : T.Exact := E.exact 1
  have hzero : T.g = 0 := (isZero_cokernel_of_epi f).eq_of_tgt _ _
  let _ : Mono S.f := inferInstance
  let _ : Epi S.g := (T.exact_iff_epi hzero).mp hT
  have hS : S.ShortExact := { exact := E.exact 0 (by decide) }
  exact P.prop_X₂_of_shortExact hS hf hg

/-- The actual inherited Quillen exact structure on an isomorphism-stable,
zero-containing, extension-closed full subcategory of an abelian category.
All admissible rows are precisely the ambient short exact rows. -/
@[instance_reducible]
def ofFullSubcategory : ExactCategory P.FullSubcategory where
  IsAdmissibleExact := fullSubcategoryAdmissible P
  shortExact_of_isAdmissibleExact := fun {S} hS => fullSubcategoryShortExact P S hS
  isLimit_kernelFork := fun {S} hS => ⟨fullSubcategoryKernel P S hS⟩
  isColimit_cokernelCofork := fun {S} hS => ⟨fullSubcategoryCokernel P S hS⟩
  isAdmissibleExact_of_iso := by
    intro S T e hS
    exact ShortComplex.shortExact_of_iso (P.ι.mapShortComplex.mapIso e) hS
  isAdmissibleExact_split X Y :=
    ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map P.ι).shortExact
  admissibleMono_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨hf, hQf⟩ := (fullSubcategoryMono_iff P f).mp hf
    obtain ⟨hg, hQg⟩ := (fullSubcategoryMono_iff P g).mp hg
    let _ : Mono f.hom := hf
    let _ : Mono g.hom := hg
    apply (fullSubcategoryMono_iff P (f ≫ g)).mpr
    change Mono (f.hom ≫ g.hom) ∧ P (cokernel (f.hom ≫ g.hom))
    exact ⟨inferInstance, cokernel_comp_mem P f.hom g.hom hQf hQg⟩
  admissibleEpi_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨hf, hKf⟩ := (fullSubcategoryEpi_iff P f).mp hf
    obtain ⟨hg, hKg⟩ := (fullSubcategoryEpi_iff P g).mp hg
    let _ : Epi f.hom := hf
    let _ : Epi g.hom := hg
    apply (fullSubcategoryEpi_iff P (f ≫ g)).mpr
    change Epi (f.hom ≫ g.hom) ∧ P (kernel (f.hom ≫ g.hom))
    exact ⟨inferInstance, kernel_comp_mem P f.hom g.hom hKf hKg⟩
  admissibleMono_pushout := by
    intro X Y i hi X' f
    obtain ⟨hi, hQ⟩ := (fullSubcategoryMono_iff P i).mp hi
    let _ : Mono i.hom := hi
    let sq := IsPushout.of_hasPushout f.hom i.hom
    let j := pushout.inl f.hom i.hom
    let k := pushout.inr f.hom i.hom
    let _ : Mono j := inferInstance
    let c := cokernel.map i.hom j f.hom k sq.flip.w
    let _ : IsIso c := isIso_cokernel_map_of_isPushout sq.flip
    have hC : P (cokernel j) := P.prop_of_iso (asIso c) hQ
    have hB : P (pushout f.hom i.hom) := P.prop_X₂_of_shortExact
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel j)
        inferInstance inferInstance) X'.property hC
    let B : P.FullSubcategory := ⟨pushout f.hom i.hom, hB⟩
    let j' : X' ⟶ B := ObjectProperty.homMk j
    let k' : Y ⟶ B := ObjectProperty.homMk k
    have hj' : Mono j'.hom := by change Mono j; infer_instance
    refine ⟨B, j', k', ?_, (fullSubcategoryMono_iff P j').mpr ⟨hj', hC⟩⟩
    exact IsPushout.of_map_of_faithful (f := f) (g := i) (h := j') (i := k') P.ι sq
  admissibleEpi_pullback := by
    intro Y Z p hp Z' g
    obtain ⟨hp, hK⟩ := (fullSubcategoryEpi_iff P p).mp hp
    let _ : Epi p.hom := hp
    let sq := IsPullback.of_hasPullback g.hom p.hom
    let j := pullback.fst g.hom p.hom
    let k := pullback.snd g.hom p.hom
    let _ : Epi j := inferInstance
    let c := kernel.map j p.hom k g.hom sq.w
    let _ : IsIso c := isIso_kernel_map_of_isPullback sq
    have hC : P (kernel j) := P.prop_of_iso (asIso c).symm hK
    have hB : P (pullback g.hom p.hom) := P.prop_X₂_of_shortExact
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel j)
        inferInstance inferInstance) hC Z'.property
    let B : P.FullSubcategory := ⟨pullback g.hom p.hom, hB⟩
    let j' : B ⟶ Z' := ObjectProperty.homMk j
    let k' : B ⟶ Y := ObjectProperty.homMk k
    have hj' : Epi j'.hom := by change Epi j; infer_instance
    refine ⟨B, j', k', ?_, (fullSubcategoryEpi_iff P j').mpr ⟨hj', hC⟩⟩
    exact IsPullback.of_map_of_faithful (f := j') (g := k') (h := g) (i := p) P.ι sq

/-- Admissibility for the named inherited exact structure is exactly
actual short exactness after the full inclusion. -/
theorem ofFullSubcategory_isAdmissibleExact_iff (S : ShortComplex P.FullSubcategory) :
    letI : ExactCategory P.FullSubcategory := ofFullSubcategory P
    ExactCategory.IsAdmissibleExact S ↔ (S.map P.ι).ShortExact := by
  rfl

end ExactCategory

end CategoryTheory

end
