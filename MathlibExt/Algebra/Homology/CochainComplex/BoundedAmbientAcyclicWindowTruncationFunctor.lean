/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindowSignedDisk
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindowCycleFunctor

/-!
# Functorial top disks and selected top-truncation kernels

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under epi kernels between its objects. For an F-acyclic complex K supported in [a,b],
project to the identity disk Dᵇ(Kᵇ) and take the selected source kernel T_b(K).

The kernel universal properties make T_b additive and natural, with inclusion κ. It has support
[a,b−1], zero top term, lower term naturally isomorphic to Zᵇ⁻¹(K), and inclusion isomorphisms
to the original terms away from b−1,b. Faithfulness supplies the top-disk support even when the
source window is degenerate.

With F exact, T_b remains F-acyclic and its shorter-window and same-window lifts preserve
admissible cofibrations and given pushouts. These lifts and the top-disk endofunctor are
Waldhausen exact in the isomorphism-weak window models. All source and ambient object and Hom
universes remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientWindowTruncation

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Evaluating K in degree b and applying the identity-disk
functor gives the raw top disk Dᵇ(Kᵇ). -/
abbrev diskRawFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ CochainComplex E ℤ :=
  { (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) b) ⋙
      SignedDisk.raw E b with
    obj := fun K => TruncationAt.topDiskRaw (b := b) K.obj.obj }

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.Full] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Assume F is faithful. If the preceding term Kᵇ⁻¹ is
zero, then acyclicity and faithfulness force the top term Kᵇ to be zero. -/
theorem topTerm_isZero_of_prev (a b : ℤ) (K : AmbientAcyclicWindow F a b)
    (hPrev : IsZero (K.obj.obj.obj.X (b - 1))) : IsZero (K.obj.obj.obj.X b) := by
  let _ : Epi (F.map (K.obj.obj.obj.d (b - 1) b)) :=
    mappedDifferential_epi_of_acyclic_of_isZero_succ F K.obj.obj b
      (K.obj.property (b + 1) (Or.inr (by omega))) K.property
  have hz : IsZero (F.obj (K.obj.obj.obj.X (b - 1))) := F.map_isZero hPrev
  have hTarget : IsZero (F.obj (K.obj.obj.obj.X b)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_epi (F.map (K.obj.obj.obj.d (b - 1) b))).mp
    simp only [Category.comp_id, comp_zero]
    exact hz.eq_of_src _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact hTarget.eq_of_src _ _

omit [ExactCategory E] [F.Full] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Assume F is faithful. The disk Dᵇ(Kᵇ) has support in
[a,b]. If its lower disk degree b−1 is outside that window, the top source term is zero and so
is the disk. -/
theorem disk_support (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    ∀ p : ℤ, p < a ∨ b < p → IsZero (((diskRawFunctor F a b).obj K).X p) := by
  intro p hp
  by_cases hLower : p = b - 1
  · subst p
    have hPrev : IsZero (K.obj.obj.obj.X (b - 1)) := K.obj.property (b - 1) hp
    exact (topTerm_isZero_of_prev F a b K hPrev).of_iso
      (TruncationAt.topDiskLowerIso (b := b) K.obj.obj).symm
  by_cases hUpper : p = b
  · subst p
    exact (K.obj.property b hp).of_iso (TruncationAt.topDiskUpperIso (b := b) K.obj.obj).symm
  exact TruncationAt.topDisk_isZero_X (b := b) K.obj.obj p hLower hUpper

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. For a window cochain map f:K→L, f≫πL=πK≫D_b(f), where π
is the top-disk projection. -/
theorem diskProjection_naturality (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    f.hom.hom.hom ≫ TruncationAt.topDiskProjection (b := b) L.obj.obj =
      TruncationAt.topDiskProjection (b := b) K.obj.obj ≫ (diskRawFunctor F a b).map f := by
  ext p
  by_cases hUpper : p = b
  · subst p
    simp only [HomologicalComplex.comp_f, TruncationAt.topDiskProjection_f_upper]
    exact (SignedDisk.upperIso_naturality E b (f.hom.hom.hom.f b)).symm
  by_cases hLower : p = b - 1
  · subst p
    simp only [HomologicalComplex.comp_f, TruncationAt.topDiskProjection_f_lower]
    have hm : f.hom.hom.hom.f b ≫ (TruncationAt.topDiskLowerIso (b := b) L.obj.obj).hom =
        (TruncationAt.topDiskLowerIso (b := b) K.obj.obj).hom ≫
          ((diskRawFunctor F a b).map f).f (b - 1) :=
      (SignedDisk.lowerIso_naturality E b (f.hom.hom.hom.f b)).symm
    calc
      _ = (f.hom.hom.hom.f (b - 1) ≫ L.obj.obj.obj.d (b - 1) b) ≫
          (TruncationAt.topDiskLowerIso (b := b) L.obj.obj).hom := (Category.assoc _ _ _).symm
      _ = (K.obj.obj.obj.d (b - 1) b ≫ f.hom.hom.hom.f b) ≫
          (TruncationAt.topDiskLowerIso (b := b) L.obj.obj).hom :=
        congrArg (fun g => g ≫ (TruncationAt.topDiskLowerIso (b := b) L.obj.obj).hom)
          (f.hom.hom.hom.comm (b - 1) b)
      _ = K.obj.obj.obj.d (b - 1) b ≫
          (f.hom.hom.hom.f b ≫ (TruncationAt.topDiskLowerIso (b := b) L.obj.obj).hom) :=
        Category.assoc _ _ _
      _ = K.obj.obj.obj.d (b - 1) b ≫
          ((TruncationAt.topDiskLowerIso (b := b) K.obj.obj).hom ≫
            ((diskRawFunctor F a b).map f).f (b - 1)) :=
        congrArg (fun g => K.obj.obj.obj.d (b - 1) b ≫ g) hm
      _ = _ := (Category.assoc _ _ _).symm
  exact (TruncationAt.topDisk_isZero_X (b := b) L.obj.obj p hLower hUpper).eq_of_tgt _ _

/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. The top projections πK:K→Dᵇ(Kᵇ) form a natural
transformation from raw inclusion to the top-disk functor. -/
def diskProjectionRaw (a b : ℤ) : ambientAcyclicWindowRaw F a b ⟶ diskRawFunctor F a b where
  app K := TruncationAt.topDiskProjection (b := b) K.obj.obj
  naturality {_K _L} f := diskProjection_naturality F a b f

/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. The top identity disk is bounded in [b−1,b], so its raw
functor lifts to bounded E-cochains. -/
def diskBoundedFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Bounded E :=
  ObjectProperty.lift (CochainComplex.bounded E) (diskRawFunctor F a b)
    (fun K => TruncationAt.bounded_topDiskRaw (b := b) K.obj.obj)

/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Assume F is faithful. The top-disk support in [a,b]
gives a lift of Dᵇ(Kᵇ) to the same support-window category. -/
def diskWindowFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Window E a b :=
  ObjectProperty.lift (windowSupport E a b) (diskBoundedFunctor F a b) (disk_support F a b)

/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Assume F is faithful. The supported top disk has
acyclic F-image by its contraction, defining an endofunctor of the F-acyclic [a,b] window. -/
def diskFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  ObjectProperty.lift (ambientAcyclicWindowObjects F a b) (diskWindowFunctor F a b)
    (fun K => TruncationAt.topDisk_map_acyclic (b := b) F K.obj.obj)

omit [ExactCategory E] [F.Full] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive with zero and binary biproducts, A abelian and F:E→A additive. Consider
F-acyclic cochains K supported in [a,b]. Assume F is faithful. Forgetting the top-disk
endofunctor to raw cochains gives the same functor K↦Dᵇ(Kᵇ). -/
theorem diskFunctor_comp_raw (a b : ℤ) :
    diskFunctor F a b ⋙ ambientAcyclicWindowRaw F a b = diskRawFunctor F a b := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The selected raw top truncation T_b(K) is the kernel cochain complex of πK. -/
abbrev kernelRawObj (a b : ℤ) (K : AmbientAcyclicWindow F a b) : CochainComplex E ℤ :=
  TruncationAt.topTruncationRaw (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The selected truncation has its kernel cochain map κK:T_b(K)→K. -/
abbrev kernelRawι (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    kernelRawObj F hKernelClosure a b K ⟶ K.obj.obj.obj :=
  TruncationAt.topTruncationRawι (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The whole cochain fork T_b(K)→K is a kernel fork of πK, with its selected universal
property. -/
abbrev kernelIsLimit (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsLimit (KernelFork.ofι (f := (diskProjectionRaw F a b).app K)
      (kernelRawι F hKernelClosure a b K)
      (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
        (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property)) :=
  TruncationAt.topTruncationKernelIsLimit (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For a cochain map f:K→L in the same window, κK≫f≫πL=0. -/
theorem kernelInclusion_map_projection (a b : ℤ) {K L : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) :
    (kernelRawι F hKernelClosure a b K ≫ f.hom.hom.hom) ≫
      (diskProjectionRaw F a b).app L = 0 := by
  change (kernelRawι F hKernelClosure a b K ≫ f.hom.hom.hom) ≫
    TruncationAt.topDiskProjection (b := b) L.obj.obj = 0
  rw [Category.assoc, diskProjection_naturality, ← Category.assoc]
  exact (congrArg (fun g => g ≫ (diskRawFunctor F a b).map f)
    (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
      (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property)).trans zero_comp

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. A window map f:K→L has the unique kernel lift T_b(f):T_b(K)→T_b(L) with
T_b(f)≫κL=κK≫f. -/
def kernelRawMap (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    kernelRawObj F hKernelClosure a b K ⟶ kernelRawObj F hKernelClosure a b L :=
  (KernelFork.IsLimit.lift' (kernelIsLimit F hKernelClosure a b L)
    (kernelRawι F hKernelClosure a b K ≫ f.hom.hom.hom)
    (kernelInclusion_map_projection F hKernelClosure a b f)).1

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For f:K→L, the selected raw kernel map satisfies T_b(f)≫κL=κK≫f. -/
theorem kernelRawMap_ι (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    kernelRawMap F hKernelClosure a b f ≫ kernelRawι F hKernelClosure a b L =
      kernelRawι F hKernelClosure a b K ≫ f.hom.hom.hom :=
  (KernelFork.IsLimit.lift' (kernelIsLimit F hKernelClosure a b L)
    (kernelRawι F hKernelClosure a b K ≫ f.hom.hom.hom)
    (kernelInclusion_map_projection F hKernelClosure a b f)).2

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The raw kernel lift of id_K is id_(T_b(K)). -/
theorem kernelRawMap_id (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    kernelRawMap F hKernelClosure a b (𝟙 K) = 𝟙 (kernelRawObj F hKernelClosure a b K) := by
  let _ : Mono (kernelRawι F hKernelClosure a b K) :=
    Fork.IsLimit.mono (s := KernelFork.ofι (kernelRawι F hKernelClosure a b K)
      (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
        (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property))
      (kernelIsLimit F hKernelClosure a b K)
  apply (cancel_mono (kernelRawι F hKernelClosure a b K)).mp
  have hid : (𝟙 K : K ⟶ K).hom.hom.hom = 𝟙 K.obj.obj.obj := rfl
  simpa only [hid, Category.comp_id, Category.id_comp] using
    kernelRawMap_ι F hKernelClosure a b (𝟙 K)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For window maps f:K→L and g:L→M, T_b(f≫g)=T_b(f)≫T_b(g). -/
theorem kernelRawMap_comp (a b : ℤ) {K L M : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) (g : L ⟶ M) :
    kernelRawMap F hKernelClosure a b (f ≫ g) =
      kernelRawMap F hKernelClosure a b f ≫ kernelRawMap F hKernelClosure a b g := by
  let _ : Mono (kernelRawι F hKernelClosure a b M) :=
    Fork.IsLimit.mono (s := KernelFork.ofι (kernelRawι F hKernelClosure a b M)
      (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
        (hSupport := M.obj.property) F hKernelClosure M.obj.obj M.property))
      (kernelIsLimit F hKernelClosure a b M)
  apply (cancel_mono (kernelRawι F hKernelClosure a b M)).mp
  rw [kernelRawMap_ι, Category.assoc, kernelRawMap_ι, ← Category.assoc,
    kernelRawMap_ι, Category.assoc]
  rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For window maps f,g:K→L, T_b(f+g)=T_b(f)+T_b(g). -/
theorem kernelRawMap_add (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f g : K ⟶ L) :
    kernelRawMap F hKernelClosure a b (f + g) =
      kernelRawMap F hKernelClosure a b f + kernelRawMap F hKernelClosure a b g := by
  let _ : Mono (kernelRawι F hKernelClosure a b L) :=
    Fork.IsLimit.mono (s := KernelFork.ofι (kernelRawι F hKernelClosure a b L)
      (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
        (hSupport := L.obj.property) F hKernelClosure L.obj.obj L.property))
      (kernelIsLimit F hKernelClosure a b L)
  apply (cancel_mono (kernelRawι F hKernelClosure a b L)).mp
  rw [Preadditive.add_comp, kernelRawMap_ι, kernelRawMap_ι, kernelRawMap_ι]
  change kernelRawι F hKernelClosure a b K ≫ (f.hom.hom.hom + g.hom.hom.hom) = _
  simp only [Preadditive.comp_add]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. Selected truncation kernels and their unique lifts define a functor from the
F-acyclic window to raw E-cochains. -/
abbrev kernelRawFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ CochainComplex E ℤ where
  obj K := kernelRawObj F hKernelClosure a b K
  map f := kernelRawMap F hKernelClosure a b f
  map_id K := kernelRawMap_id F hKernelClosure a b K
  map_comp f g := kernelRawMap_comp F hKernelClosure a b f g

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The selected raw truncation-kernel functor is additive. -/
instance kernelRawFunctor_additive (a b : ℤ) :
    (kernelRawFunctor F hKernelClosure a b).Additive where
  map_add {_K _L} f g := by exact kernelRawMap_add F hKernelClosure a b f g

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The selected inclusions κK form a natural transformation from the raw truncation
functor to raw inclusion of the source window. -/
def kernelInclusionRaw (a b : ℤ) :
    kernelRawFunctor F hKernelClosure a b ⟶ ambientAcyclicWindowRaw F a b where
  app K := kernelRawι F hKernelClosure a b K
  naturality {_K _L} f := kernelRawMap_ι F hKernelClosure a b f

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. Every term of T_b(K) is zero outside [a,b−1]. -/
theorem kernel_support (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    ∀ p : ℤ, p < a ∨ b - 1 < p →
      IsZero (((kernelRawFunctor F hKernelClosure a b).obj K).X p) :=
  TruncationAt.topTruncationRaw_support (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The shorter support makes T_b(K) a bounded complex, giving the corresponding
bounded-kernel functor. -/
def kernelBoundedFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Bounded E :=
  ObjectProperty.lift (CochainComplex.bounded E) (kernelRawFunctor F hKernelClosure a b)
    (fun K => TruncationAt.bounded_topTruncationRaw (b := b) (a := a)
      (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The support [a,b−1] lifts T_b(K) to the strictly shorter support-window category. -/
def shorterWindowFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Window E a (b - 1) :=
  ObjectProperty.lift (windowSupport E a (b - 1)) (kernelBoundedFunctor F hKernelClosure a b)
    (kernel_support F hKernelClosure a b)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The F-image of T_b(K) is acyclic, so the selected truncation defines
a functor C(a,b)→C(a,b−1). -/
def shorterFunctor (a b : ℤ) :
    AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a (b - 1) :=
  ObjectProperty.lift (ambientAcyclicWindowObjects F a (b - 1))
    (shorterWindowFunctor F hKernelClosure a b)
    (fun K => TruncationAt.topTruncation_map_acyclic (b := b) (a := a)
      (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. Forgetting shorter-window truncation to raw cochains gives the same
selected raw kernel T_b. -/
theorem shorterFunctor_comp_raw (a b : ℤ) :
    shorterFunctor F hKernelClosure a b ⋙ ambientAcyclicWindowRaw F a (b - 1) =
      kernelRawFunctor F hKernelClosure a b := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. In each integer degree p, κKᵖ:T_b(K)ᵖ→Kᵖ gives a kernel fork of the component πKᵖ. -/
abbrev termFork (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) :
    KernelFork (((diskProjectionRaw F a b).app K).f p) :=
  KernelFork.ofι ((kernelRawι F hKernelClosure a b K).f p)
    (congrArg (fun g => g.f p)
      (TruncationAt.topTruncationRawι_projection (b := b) (a := a)
        (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The selected degree-p kernel fork of πKᵖ is limiting for every p. -/
abbrev termIsLimit (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) :
    IsLimit (termFork F hKernelClosure a b K p) :=
  TruncationAt.topTruncationTermIsLimit (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property p

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The top truncation term T_b(K)ᵇ is zero, since πKᵇ is an isomorphism onto the upper
disk term. -/
theorem upper_isZero (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsZero (((kernelRawFunctor F hKernelClosure a b).obj K).X b) :=
  TruncationAt.topTruncationRaw_isZero_X_upper (b := b) (a := a) (hSupport := K.obj.property)
    F hKernelClosure K.obj.obj K.property

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For p≠b−1 and p≠b, the inclusion κKᵖ:T_b(K)ᵖ→Kᵖ is an isomorphism. -/
theorem term_isIso (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ)
    (hLower : p ≠ b - 1) (hUpper : p ≠ b) :
    IsIso ((kernelRawι F hKernelClosure a b K).f p) := by
  have hz : ((diskProjectionRaw F a b).app K).f p = 0 :=
    (TruncationAt.topDisk_isZero_X (b := b) K.obj.obj p hLower hUpper).eq_of_tgt _ _
  exact KernelFork.IsLimit.isIso_ι (termFork F hKernelClosure a b K p)
    (termIsLimit F hKernelClosure a b K p) hz

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The original source cycle inclusion Zᵇ⁻¹(K)→Kᵇ⁻¹ also represents the kernel of the
lower disk-projection component πKᵇ⁻¹. -/
def lowerCycleIsLimit (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsLimit (KernelFork.ofι (f := ((diskProjectionRaw F a b).app K).f (b - 1))
      (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).ι (by
        change (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).ι ≫
          (TruncationAt.topDiskProjection (b := b) K.obj.obj).f (b - 1) = 0
        rw [TruncationAt.topDiskProjection_f_lower, ← Category.assoc]
        have h : (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).ι ≫
            K.obj.obj.obj.d (b - 1) b = 0 := by
          have aux (t : ℤ) (ht : b - 1 + 1 = t) :
              (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).ι ≫
                K.obj.obj.obj.d (b - 1) t = 0 := by
            subst t
            exact (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).zero
          exact aux b (by omega)
        rw [h, zero_comp])) := by
  let D := AmbientWindowCycles.data F hKernelClosure a b (b - 1) K
  have hKernel := KernelFork.isLimitOfIsLimitOfIff'
    (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b (b - 1) K)
    (K.obj.obj.obj.d (b - 1) b) (by
      intro W φ
      have aux (t : ℤ) (ht : b - 1 + 1 = t) :
          φ ≫ K.obj.obj.obj.d (b - 1) (b - 1 + 1) = 0 ↔
            φ ≫ K.obj.obj.obj.d (b - 1) t = 0 := by
        subst t
        rfl
      exact aux b (by omega))
  let _ : Mono (TruncationAt.topDiskLowerIso (b := b) K.obj.obj).hom := inferInstance
  exact isKernelCompMono hKernel (TruncationAt.topDiskLowerIso (b := b) K.obj.obj).hom
    (TruncationAt.topDiskProjection_f_lower (b := b) K.obj.obj)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. Comparing the two selected kernels of πKᵇ⁻¹ gives T_b(K)ᵇ⁻¹≅Zᵇ⁻¹(K). -/
def lowerCycleIso (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    ((kernelRawFunctor F hKernelClosure a b).obj K).X (b - 1) ≅
      (AmbientWindowCycles.functor F hKernelClosure a b (b - 1)).obj K :=
  (termIsLimit F hKernelClosure a b K (b - 1)).conePointUniqueUpToIso
    (lowerCycleIsLimit F hKernelClosure a b K)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. The lower chart T_b(K)ᵇ⁻¹→Zᵇ⁻¹(K) followed by the original cycle inclusion is κKᵇ⁻¹. -/
theorem lowerCycleIso_hom_ι (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    (lowerCycleIso F hKernelClosure a b K).hom ≫
      (AmbientWindowCycles.data F hKernelClosure a b (b - 1) K).ι =
    (kernelRawι F hKernelClosure a b K).f (b - 1) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (termIsLimit F hKernelClosure a b K (b - 1))
    (lowerCycleIsLimit F hKernelClosure a b K) WalkingParallelPair.zero

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. Evaluation of the raw truncation functor at b−1 is naturally isomorphic to the
original degree-b−1 source-cycle functor. -/
def lowerCycleNatIso (a b : ℤ) :
    kernelRawFunctor F hKernelClosure a b ⋙ HomologicalComplex.eval E (.up ℤ) (b - 1) ≅
      AmbientWindowCycles.functor F hKernelClosure a b (b - 1) :=
  NatIso.ofComponents (lowerCycleIso F hKernelClosure a b) (fun {_K _L} f => by
    let _ : Mono (AmbientWindowCycles.data F hKernelClosure a b (b - 1) _L).ι :=
      Fork.IsLimit.mono (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b (b - 1) _L)
    apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure a b (b - 1) _L).ι).mp
    have hKernel : ((kernelRawFunctor F hKernelClosure a b).map f).f (b - 1) ≫
        (kernelRawι F hKernelClosure a b _L).f (b - 1) =
      (kernelRawι F hKernelClosure a b _K).f (b - 1) ≫ f.hom.hom.hom.f (b - 1) :=
      congrArg (fun g => g.f (b - 1)) (kernelRawMap_ι F hKernelClosure a b f)
    change (((kernelRawFunctor F hKernelClosure a b).map f).f (b - 1) ≫
        (lowerCycleIso F hKernelClosure a b _L).hom) ≫ _ =
      ((lowerCycleIso F hKernelClosure a b _K).hom ≫
        AmbientWindowCycles.map F hKernelClosure a b (b - 1) f) ≫ _
    rw [Category.assoc, lowerCycleIso_hom_ι, hKernel, Category.assoc,
      AmbientWindowCycles.map_ι, ← Category.assoc, lowerCycleIso_hom_ι])

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. For p≠b−1,b, the degree-p truncation inclusions give a natural isomorphism from
evaluation of T_b to original raw degree-p evaluation. -/
def termNatIso (a b p : ℤ) (hLower : p ≠ b - 1) (hUpper : p ≠ b) :
    kernelRawFunctor F hKernelClosure a b ⋙ HomologicalComplex.eval E (.up ℤ) p ≅
      ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p := by
  let _ : ∀ K : AmbientAcyclicWindow F a b,
      IsIso ((kernelRawι F hKernelClosure a b K).f p) :=
    fun K => term_isIso F hKernelClosure a b K p hLower hUpper
  exact NatIso.ofComponents (fun K => asIso ((kernelRawι F hKernelClosure a b K).f p))
    (fun {_K _L} f => congrArg (fun g => g.f p) (kernelRawMap_ι F hKernelClosure a b f))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. If f is a cofibration in the degreewise-admissible window model,
every component of T_b(f) is an admissible mono in E. -/
theorem kernelRawMap_isAdmissibleMono_f (a b : ℤ) {K L : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) (hf : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration f) (p : ℤ) :
    IsAdmissibleMono (((kernelRawFunctor F hKernelClosure a b).map f).f p) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  by_cases hLower : p = b - 1
  · subst p
    let eK := (lowerCycleNatIso F hKernelClosure a b).app K
    let eL := (lowerCycleNatIso F hKernelClosure a b).app L
    have hChart : ((kernelRawFunctor F hKernelClosure a b).map f).f (b - 1) =
        eK.hom ≫ AmbientWindowCycles.map F hKernelClosure a b (b - 1) f ≫ eL.inv := by
      apply (cancel_mono eL.hom).mp
      have hn := (lowerCycleNatIso F hKernelClosure a b).hom.naturality f
      change ((kernelRawFunctor F hKernelClosure a b).map f).f (b - 1) ≫ eL.hom =
        eK.hom ≫ AmbientWindowCycles.map F hKernelClosure a b (b - 1) f at hn
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
    rw [hChart]
    exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso eK.hom)
      (admissibleMono_comp.comp_mem _ _
        (AmbientWindowCycles.map_isAdmissibleMono F hKernelClosure a b (b - 1) f hf)
        (IsAdmissibleMono.of_isIso eL.inv))
  by_cases hUpper : p = b
  · subst p
    let e := (upper_isZero F hKernelClosure a b K).isoZero
    have h : IsAdmissibleMono
        (e.inv ≫ ((kernelRawFunctor F hKernelClosure a b).map f).f b) :=
      IsAdmissibleMono.fromZero _
    have hc := admissibleMono_comp.comp_mem e.hom _
      (IsAdmissibleMono.of_isIso e.hom) h
    change IsAdmissibleMono
      (e.hom ≫ (e.inv ≫ ((kernelRawFunctor F hKernelClosure a b).map f).f b)) at hc
    simpa only [Iso.hom_inv_id_assoc] using hc
  let eK := (termNatIso F hKernelClosure a b p hLower hUpper).app K
  let eL := (termNatIso F hKernelClosure a b p hLower hUpper).app L
  have hChart : ((kernelRawFunctor F hKernelClosure a b).map f).f p =
      eK.hom ≫ f.hom.hom.hom.f p ≫ eL.inv := by
    apply (cancel_mono eL.hom).mp
    have hn := (termNatIso F hKernelClosure a b p hLower hUpper).hom.naturality f
    change ((kernelRawFunctor F hKernelClosure a b).map f).f p ≫ eL.hom =
      eK.hom ≫ f.hom.hom.hom.f p at hn
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
  rw [hChart]
  exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso eK.hom)
    (admissibleMono_comp.comp_mem _ _
      ((ambientAcyclicWindow_isCofibration_iff F a b f).mp hf p)
      (IsAdmissibleMono.of_isIso eL.inv))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. A given window pushout along a cofibration evaluates, after T_b, to a
pushout in E in every degree p. -/
theorem kernelRawFunctor_map_term_isPushout (a b : ℤ)
    {K L M P : AmbientAcyclicWindow F a b}
    {i : K ⟶ L} {f : K ⟶ M} {inL : L ⟶ P} {inM : M ⟶ P}
    (hi : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration i) (hP : IsPushout i f inL inM) (p : ℤ) :
    IsPushout (((kernelRawFunctor F hKernelClosure a b).map i).f p)
      (((kernelRawFunctor F hKernelClosure a b).map f).f p)
      (((kernelRawFunctor F hKernelClosure a b).map inL).f p)
      (((kernelRawFunctor F hKernelClosure a b).map inM).f p) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  by_cases hLower : p = b - 1
  · subst p
    let e := lowerCycleNatIso F hKernelClosure a b
    apply (AmbientWindowCycles.map_isPushout F hKernelClosure a b (b - 1) hi hP).of_iso'
      (e.app K) (e.app L) (e.app M) (e.app P)
    · exact (e.hom.naturality i).symm
    · exact (e.hom.naturality f).symm
    · exact (e.hom.naturality inL).symm
    · exact (e.hom.naturality inM).symm
  by_cases hUpper : p = b
  · subst p
    let _ : IsIso (((kernelRawFunctor F hKernelClosure a b).map i).f b) :=
      (upper_isZero F hKernelClosure a b K).isIso
        (upper_isZero F hKernelClosure a b L) _
    let _ : IsIso (((kernelRawFunctor F hKernelClosure a b).map inM).f b) :=
      (upper_isZero F hKernelClosure a b M).isIso
        (upper_isZero F hKernelClosure a b P) _
    apply IsPushout.of_horiz_isIso
    constructor
    have h : (kernelRawFunctor F hKernelClosure a b).map i ≫
        (kernelRawFunctor F hKernelClosure a b).map inL =
      (kernelRawFunctor F hKernelClosure a b).map f ≫
        (kernelRawFunctor F hKernelClosure a b).map inM := by
      simpa only [kernelRawMap_comp] using
        congrArg (kernelRawMap F hKernelClosure a b) hP.w
    exact congrArg (fun z => z.f b) h
  let e := termNatIso F hKernelClosure a b p hLower hUpper
  apply (ambientAcyclicWindowPushout_term F a b
    ((ambientAcyclicWindow_isCofibration_iff F a b i).mp hi) hP p).of_iso'
      (e.app K) (e.app L) (e.app M) (e.app P)
  · exact (e.hom.naturality i).symm
  · exact (e.hom.naturality f).symm
  · exact (e.hom.naturality inL).symm
  · exact (e.hom.naturality inM).symm

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The selected raw truncation functor sends any given window pushout
along a cofibration to a pushout of whole raw cochain complexes. -/
theorem kernelRawFunctor_map_isPushout (a b : ℤ)
    {K L M P : AmbientAcyclicWindow F a b}
    {i : K ⟶ L} {f : K ⟶ M} {inL : L ⟶ P} {inM : M ⟶ P}
    (hi : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration i) (hP : IsPushout i f inL inM) :
    IsPushout ((kernelRawFunctor F hKernelClosure a b).map i)
      ((kernelRawFunctor F hKernelClosure a b).map f)
      ((kernelRawFunctor F hKernelClosure a b).map inL)
      ((kernelRawFunctor F hKernelClosure a b).map inM) := by
  let T := kernelRawFunctor F hKernelClosure a b
  let c := T.mapCocone hP.cocone
  have hc : IsColimit c := HomologicalComplex.isColimitOfEval _ c (fun p => by
    let G := T ⋙ HomologicalComplex.eval E (.up ℤ) p
    let _ : PreservesColimit (span i f) G :=
      (hP.preservesColimit_span_iff (F := G)).mpr
        (kernelRawFunctor_map_term_isPushout F hKernelClosure a b hi hP p)
    exact isColimitOfPreserves G hP.isColimit)
  let _ : PreservesColimit (span i f) T :=
    preservesColimit_of_preserves_colimit_cocone hP.isColimit hc
  exact hP.map T

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The shorter-window truncation C(a,b)→C(a,b−1) is Waldhausen exact for
componentwise admissible cofibrations and isomorphism weak maps. -/
theorem shorterFunctor_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := ambientAcyclicWindowWaldhausenCategory F a (b - 1)
    (shorterFunctor F hKernelClosure a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := ambientAcyclicWindowWaldhausenCategory F a (b - 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowRaw F a (b - 1)) _
      ((kernelRawFunctor F hKernelClosure a b).map_isZero hK)
  · intro K L f hf
    apply (ambientAcyclicWindow_isCofibration_iff F a (b - 1) _).mpr
    exact kernelRawMap_isAdmissibleMono_f F hKernelClosure a b f hf
  · intro K L f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    exact (ambientAcyclicWindow_isWeakEquivalence_iff F a (b - 1) _).mpr inferInstance
  · intro K L M P i f inM inL hi hP
    apply IsPushout.of_map_of_faithful (ambientAcyclicWindowRaw F a (b - 1))
    exact (kernelRawFunctor_map_isPushout F hKernelClosure a b hi hP.flip).flip

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Write πK:K→Dᵇ(Kᵇ) for the top-disk projection and κK:T_b(K)→K for its selected kernel
inclusion. Include the selected shorter-support kernel T_b(K) back into the original support
window [a,b]. -/
def fullWindowFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Window E a b :=
  ObjectProperty.lift (windowSupport E a b) (kernelBoundedFunctor F hKernelClosure a b)
    (fun K p hp => kernel_support F hKernelClosure a b K p (by
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by omega)))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The selected truncation, included back in [a,b], defines the
same-window F-acyclic endofunctor T_b:C(a,b)→C(a,b). -/
def fullTruncationFunctor (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  ObjectProperty.lift (ambientAcyclicWindowObjects F a b)
    (fullWindowFunctor F hKernelClosure a b)
    (fun K => TruncationAt.topTruncation_map_acyclic (b := b) (a := a)
      (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. Forgetting the same-window truncation to raw cochains gives the same
selected kernel functor T_b. -/
theorem fullTruncationFunctor_comp_raw (a b : ℤ) :
    fullTruncationFunctor F hKernelClosure a b ⋙ ambientAcyclicWindowRaw F a b =
      kernelRawFunctor F hKernelClosure a b := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The kernel maps κK:T_b(K)→K form a natural transformation from
same-window truncation to the identity functor. -/
def kernelInclusion (a b : ℤ) :
    fullTruncationFunctor F hKernelClosure a b ⟶ Functor.id (AmbientAcyclicWindow F a b) where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    (ObjectProperty.homMk (kernelRawι F hKernelClosure a b K)))
  naturality {_K _L} f := by
    apply (ambientAcyclicWindowRaw F a b).map_injective
    exact kernelRawMap_ι F hKernelClosure a b f

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The top-disk maps πK:K→D_b(K) form a natural transformation from
identity to the top-disk endofunctor. -/
def diskProjection (a b : ℤ) :
    Functor.id (AmbientAcyclicWindow F a b) ⟶ diskFunctor F a b where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    (ObjectProperty.homMk ((diskProjectionRaw F a b).app K)))
  naturality {_K _L} f := by
    apply (ambientAcyclicWindowRaw F a b).map_injective
    exact diskProjection_naturality F a b f

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The same-window top truncation is Waldhausen exact in the
componentwise-admissible and isomorphism-weak window model. -/
theorem fullTruncationFunctor_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    (fullTruncationFunctor F hKernelClosure a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowRaw F a b) _
      ((kernelRawFunctor F hKernelClosure a b).map_isZero hK)
  · intro K L f hf
    apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
    exact kernelRawMap_isAdmissibleMono_f F hKernelClosure a b f hf
  · intro K L f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    exact (ambientAcyclicWindow_isWeakEquivalence_iff F a b _).mpr inferInstance
  · intro K L M P i f inM inL hi hP
    apply IsPushout.of_map_of_faithful (ambientAcyclicWindowRaw F a b)
    exact (kernelRawFunctor_map_isPushout F hKernelClosure a b hi hP.flip).flip

omit [F.Full] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Let K be F-acyclic and supported in
[a,b]. Assume F is exact. Write T_b(K) for its selected top-truncation kernel and D_b(K)=Dᵇ(Kᵇ)
for its top identity disk. The top-disk endofunctor is Waldhausen exact in this model, including
singleton and reversed source windows. -/
theorem diskFunctor_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    (diskFunctor F a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    have hTerm : IsZero (K.obj.obj.obj.X b) :=
      (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) b).map_isZero hK
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowRaw F a b) _
      ((SignedDisk.raw E b).map_isZero hTerm)
  · intro K L f hf
    apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
    exact SignedDisk.raw_map_isAdmissibleMono_f E b (f.hom.hom.hom.f b)
      ((ambientAcyclicWindow_isCofibration_iff F a b f).mp hf b)
  · intro K L f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    exact (ambientAcyclicWindow_isWeakEquivalence_iff F a b _).mpr inferInstance
  · intro K L M P i f inM inL hi hP
    apply IsPushout.of_map_of_faithful (ambientAcyclicWindowRaw F a b)
    exact (SignedDisk.raw_map_isPushout E b
      (ambientAcyclicWindowPushout_term F a b
        ((ambientAcyclicWindow_isCofibration_iff F a b i).mp hi) hP.flip b)).flip

end CochainComplex.Bounded.AmbientWindowTruncation

end
