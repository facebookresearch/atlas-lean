/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.KernelImage
public meta import Mathlib.Tactic.DSimpPercent

/-!
# Canonical cycles, image, and homology sequences

Both sequences use the maps of an arbitrary short complex in an
abelian category. Kernel-image exactness comes from the generic arrow API;
image-to-cycles and homology use abelianImageToKernel and cokernel data.
functorEquivalence supplies the natural sequence functors.
Only the cycles-to-image sequence has a projective-image splitting.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cycles inclusion and quotient onto the outgoing map's image. -/
def cyclesImageSES (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk S.iCycles (Abelian.factorThruImage S.g) (by
    have h : (S.iCycles ≫ Abelian.factorThruImage S.g) ≫ Abelian.image.ι S.g = 0 := by
      rw [Category.assoc, Abelian.image.fac]
      exact S.iCycles_g
    exact zero_of_comp_mono _ h)

/-- The kernel/cycles comparison identifies the two sequence data. -/
def kernelImageCyclesIso (S : ShortComplex C) :
    Abelian.kernelImageSES S.g ≅ cyclesImageSES S := by
  let e : kernel S.g ≅ S.cycles := S.isoCyclesOfIsLimit (kf := KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) (kernelIsKernel S.g)
  refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_
  · change e.hom ≫ S.iCycles = kernel.ι S.g ≫ 𝟙 _
    exact (S.isoCyclesOfIsLimit_hom_iCycles (kf := KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) (kernelIsKernel S.g)).trans
      (Category.comp_id _).symm
  · change (𝟙 S.X₂) ≫ Abelian.factorThruImage S.g =
      Abelian.factorThruImage S.g ≫ 𝟙 _
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Cycles-to-image exactness is inherited from the canonical arrow sequence. -/
theorem cyclesImageSES_shortExact (S : ShortComplex C) : (cyclesImageSES S).ShortExact :=
  ShortComplex.shortExact_of_iso (kernelImageCyclesIso S)
    (Abelian.kernelImageSES_shortExact S.g)

/-- The existing short-exact universal property is the kernel certificate. -/
def cyclesImageSESIsKernel (S : ShortComplex C) :
    IsLimit (KernelFork.ofι (cyclesImageSES S).f (cyclesImageSES S).zero) :=
  (cyclesImageSES_shortExact S).fIsKernel

/-- Only projectivity of the outgoing image is needed for this splitting. -/
def cyclesImageSESSplitting (S : ShortComplex C) [Projective (Abelian.image S.g)] :
    (cyclesImageSES S).Splitting :=
  letI : Projective (cyclesImageSES S).X₃ := by
    change Projective (Abelian.image S.g)
    infer_instance
  (cyclesImageSES_shortExact S).splittingOfProjective

/-- The cycles-to-image sequence is functorial through the existing natural inclusion/quotient. -/
def cyclesImageSESFunctor : ShortComplex C ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (ShortComplex C) C).functor.obj
    (ShortComplex.mk (iCyclesNatTrans C)
      (Functor.whiskerLeft (gFunctor (C := C)) (Abelian.factorThruImageNatTrans (C := C))) (by
        apply NatTrans.ext
        funext S
        exact (cyclesImageSES S).zero))

/-- The boundary map reuses the image-to-kernel and kernel/cycles maps. -/
def boundaryCyclesMap (S : ShortComplex C) : Abelian.image S.f ⟶ S.cycles :=
  S.abelianImageToKernel ≫ (S.isoCyclesOfIsLimit (kf := KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) (kernelIsKernel S.g)).hom

/-- The boundary map followed by cycles inclusion is the image inclusion. -/
@[reassoc]
theorem boundaryCyclesMap_i (S : ShortComplex C) :
    boundaryCyclesMap S ≫ S.iCycles = Abelian.image.ι S.f := by
  dsimp only [boundaryCyclesMap]
  rw [Category.assoc, S.isoCyclesOfIsLimit_hom_iCycles (kf := KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) (kernelIsKernel S.g)]
  exact S.abelianImageToKernel_comp_kernel_ι

/-- The canonical map onto boundaries followed by their inclusion into cycles is toCycles. -/
@[reassoc]
theorem factorThruImage_boundaryCyclesMap (S : ShortComplex C) :
    Abelian.factorThruImage S.f ≫ boundaryCyclesMap S = S.toCycles := by
  apply (cancel_mono S.iCycles).1
  simpa only [Category.assoc, boundaryCyclesMap_i, Abelian.image.fac]
    using S.toCycles_i.symm

/-- Boundaries give the zero homology class, using the homology quotient. -/
@[reassoc]
theorem boundaryCyclesMap_homologyπ (S : ShortComplex C) :
    boundaryCyclesMap S ≫ S.homologyπ = 0 := by
  apply (cancel_epi (Abelian.factorThruImage S.f)).1
  simpa only [← Category.assoc, factorThruImage_boundaryCyclesMap,
    CategoryTheory.Limits.comp_zero] using S.toCycles_comp_homologyπ

/-- The image, cycles, and homology sequence. -/
def imageCyclesHomologySES (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (boundaryCyclesMap S) S.homologyπ (boundaryCyclesMap_homologyπ S)

/-- The same homology quotient is the cokernel after factoring through boundaries. -/
def imageCyclesHomologySESCokernel (S : ShortComplex C) :
    IsColimit (CokernelCofork.ofπ (imageCyclesHomologySES S).g
      (imageCyclesHomologySES S).zero) :=
  isCokernelOfComp (Abelian.factorThruImage S.f) S.toCycles S.homologyIsCokernel
    (boundaryCyclesMap_homologyπ S) (factorThruImage_boundaryCyclesMap S)

/-- Exactness of the image/cycles/homology sequence needs no projectivity. -/
theorem imageCyclesHomologySES_shortExact (S : ShortComplex C) :
    (imageCyclesHomologySES S).ShortExact := by
  have hm : Mono (boundaryCyclesMap S) := by
    change Mono (S.abelianImageToKernel ≫ (S.isoCyclesOfIsLimit (kf := KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) (kernelIsKernel S.g)).hom)
    infer_instance
  have he : Epi S.homologyπ := inferInstance
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (imageCyclesHomologySESCokernel S)) hm he

/-- The image map and cycles map commute with the boundary inclusion. -/
@[reassoc]
theorem boundaryCyclesMap_naturality {S T : ShortComplex C} (φ : S ⟶ T) :
    dsimp% only [Abelian.im_obj, fFunctor, Arrow.mk] (
    (Abelian.im (C := C)).map ((fFunctor (C := C)).map φ) ≫ boundaryCyclesMap T =
      boundaryCyclesMap S ≫ cyclesMap φ) := by
  let square : Arrow.mk S.f ⟶ Arrow.mk T.f :=
    Arrow.homMk φ.τ₁ φ.τ₂ φ.comm₁₂
  let m : Abelian.image S.f ⟶ Abelian.image T.f := (Abelian.im (C := C)).map square
  change m ≫ boundaryCyclesMap T = boundaryCyclesMap S ≫ cyclesMap φ
  have hImage : m ≫ Abelian.image.ι T.f = Abelian.image.ι S.f ≫ φ.τ₂ := by
    exact Abelian.kernelImageSESFunctor_map_image_ι square
  apply (cancel_mono T.iCycles).1
  have hLeft : (m ≫ boundaryCyclesMap T) ≫ T.iCycles =
      Abelian.image.ι S.f ≫ φ.τ₂ :=
    (Category.assoc m (boundaryCyclesMap T) T.iCycles).trans
      ((congrArg (fun z : Abelian.image T.f ⟶ T.X₂ => m ≫ z)
        (boundaryCyclesMap_i T)).trans hImage)
  have hRight : (boundaryCyclesMap S ≫ cyclesMap φ) ≫ T.iCycles =
      Abelian.image.ι S.f ≫ φ.τ₂ :=
    (Category.assoc (boundaryCyclesMap S) (cyclesMap φ) T.iCycles).trans
      ((congrArg (fun z : S.cycles ⟶ T.X₂ => boundaryCyclesMap S ≫ z)
        (ShortComplex.cyclesMap_i φ)).trans
          ((Category.assoc (boundaryCyclesMap S) S.iCycles φ.τ₂).symm.trans
            (congrArg (fun z : Abelian.image S.f ⟶ S.X₂ => z ≫ φ.τ₂)
              (boundaryCyclesMap_i S))))
  exact hLeft.trans hRight.symm

/-- The boundary map as an natural transformation on short complexes. -/
def boundaryCyclesNatTrans : fFunctor (C := C) ⋙ Abelian.im ⟶ cyclesFunctor C where
  app S := boundaryCyclesMap S
  naturality S T φ := boundaryCyclesMap_naturality φ

/-- The existing homology quotient packaged as its natural transformation. -/
def cyclesToHomologyNatTrans : cyclesFunctor C ⟶ homologyFunctor C where
  app S := S.homologyπ
  naturality S T φ := (ShortComplex.homologyπ_naturality φ).symm

/-- FunctorEquivalence packages the image/cycles/homology maps. -/
def imageCyclesHomologySESFunctor : ShortComplex C ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (ShortComplex C) C).functor.obj
    (ShortComplex.mk (boundaryCyclesNatTrans (C := C)) (cyclesToHomologyNatTrans (C := C)) (by
      apply NatTrans.ext
      funext S
      change boundaryCyclesMap S ≫ S.homologyπ = 0
      exact boundaryCyclesMap_homologyπ S))

/-- The packaged functor retains the sequence data at every short complex. -/
theorem imageCyclesHomologySESFunctor_obj (S : ShortComplex C) :
    (imageCyclesHomologySESFunctor (C := C)).obj S = imageCyclesHomologySES S := rfl

end CategoryTheory.ShortComplex
