/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The kernel-image short exact sequence

The kernel inclusion and quotient onto the image of a morphism form a
short exact sequence. Kernel and image maps make this sequence functorial
on the arrow category. A projective image gives a splitting.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Abelian

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : C}

/-- The kernel inclusion and canonical quotient onto the image. -/
def kernelImageSES (g : X ⟶ Y) : ShortComplex C :=
  ShortComplex.mk (kernel.ι g) (Abelian.factorThruImage g) (by
    have h : (kernel.ι g ≫ Abelian.factorThruImage g) ≫ Abelian.image.ι g = 0 := by
      rw [Category.assoc, Abelian.image.fac]
      exact kernel.condition g
    exact zero_of_comp_mono _ h)

/-- The first arrow is the kernel inclusion. -/
theorem kernelImageSES_f (g : X ⟶ Y) : (kernelImageSES g).f = kernel.ι g := rfl

/-- The second arrow is the canonical map onto the image. -/
theorem kernelImageSES_g (g : X ⟶ Y) :
    (kernelImageSES g).g = Abelian.factorThruImage g := rfl

/-- The canonical quotient followed by image inclusion recovers the arrow. -/
@[reassoc]
theorem kernelImageSES_g_comp (g : X ⟶ Y) :
    (kernelImageSES g).g ≫ Abelian.image.ι g = g :=
  Abelian.image.fac g

/-- The kernel remains the kernel after factoring through the image. -/
def kernelImageSESIsKernel (g : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelImageSES g).f (kernelImageSES g).zero) :=
  isKernelOfComp (Abelian.image.ι g) g (kernelIsKernel g)
    (kernelImageSES g).zero (Abelian.image.fac g)

/-- The kernel, domain, and image form a short exact sequence. -/
theorem kernelImageSES_shortExact (g : X ⟶ Y) : (kernelImageSES g).ShortExact := by
  have hm : Mono (kernel.ι g) := inferInstance
  have he : Epi (Abelian.factorThruImage g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelImageSESIsKernel g)) hm he

/-- The canonical image quotient is natural for every commutative arrow square. -/
def factorThruImageNatTrans : Arrow.leftFunc (C := C) ⟶ Abelian.im (C := C) where
  app a := Abelian.factorThruImage a.hom
  naturality {a b} t := by
    change t.left ≫ Abelian.factorThruImage b.hom =
      Abelian.factorThruImage a.hom ≫ (Abelian.im (C := C)).map t
    apply (cancel_mono (Abelian.image.ι b.hom)).1
    have hImage : (Abelian.im (C := C)).map t ≫ Abelian.image.ι b.hom =
        Abelian.image.ι a.hom ≫ t.right := by
      dsimp only [Abelian.im, Abelian.image.ι]
      exact kernel.lift_ι _ _ _
    have hLeft : (t.left ≫ Abelian.factorThruImage b.hom) ≫ Abelian.image.ι b.hom =
        a.hom ≫ t.right :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun s : b.left ⟶ b.right => t.left ≫ s)
          (Abelian.image.fac b.hom)).trans t.w)
    have hRight : (Abelian.factorThruImage a.hom ≫ (Abelian.im (C := C)).map t) ≫
        Abelian.image.ι b.hom = a.hom ≫ t.right :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun s : Abelian.image a.hom ⟶ b.right =>
          Abelian.factorThruImage a.hom ≫ s) hImage).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun s : a.left ⟶ a.right => s ≫ t.right)
              (Abelian.image.fac a.hom))))
    exact hLeft.trans hRight.symm

/-- The canonical short exact data are functorial through the kernel and image maps. -/
def kernelImageSESFunctor : Arrow C ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (Arrow C) C).functor.obj
    (ShortComplex.mk (Limits.ker.ι C) (factorThruImageNatTrans (C := C)) (by
      apply NatTrans.ext
      funext a
      exact (kernelImageSES a.hom).zero))

/-- The functor's object is precisely the arrow's kernel-image sequence. -/
theorem kernelImageSESFunctor_obj (a : Arrow C) :
    (kernelImageSESFunctor (C := C)).obj a = kernelImageSES a.hom := rfl

/-- The middle component retains the given domain map of the arrow square. -/
theorem kernelImageSESFunctor_map_τ₂ {a b : Arrow C} (t : a ⟶ b) :
    ((kernelImageSESFunctor (C := C)).map t).τ₂ = t.left := rfl

/-- The kernel component is the map induced by the domain map. -/
@[reassoc]
theorem kernelImageSESFunctor_map_kernel_ι {a b : Arrow C} (t : a ⟶ b) :
    ((kernelImageSESFunctor (C := C)).map t).τ₁ ≫ kernel.ι b.hom =
      kernel.ι a.hom ≫ t.left := by
  change (Limits.ker (C := C)).map t ≫ kernel.ι b.hom = kernel.ι a.hom ≫ t.left
  exact (Limits.ker.ι C).naturality t

/-- The image component is the map induced by the codomain map. -/
@[reassoc]
theorem kernelImageSESFunctor_map_image_ι {a b : Arrow C} (t : a ⟶ b) :
    ((kernelImageSESFunctor (C := C)).map t).τ₃ ≫ Abelian.image.ι b.hom =
      Abelian.image.ι a.hom ≫ t.right := by
  change (Abelian.im (C := C)).map t ≫ Abelian.image.ι b.hom =
    Abelian.image.ι a.hom ≫ t.right
  dsimp only [Abelian.im, Abelian.image.ι]
  exact kernel.lift_ι _ _ _

/-- Projectivity of the image gives the noncanonical splitting. -/
def kernelImageSESSplitting (g : X ⟶ Y) [Projective (Abelian.image g)] :
    (kernelImageSES g).Splitting :=
  letI : Projective (kernelImageSES g).X₃ := by
    change Projective (Abelian.image g)
    infer_instance
  (kernelImageSES_shortExact g).splittingOfProjective

/-- Its section lifts the image inclusion through the arrow. -/
@[reassoc]
theorem kernelImageSESSplitting_s_comp (g : X ⟶ Y) [Projective (Abelian.image g)] :
    (kernelImageSESSplitting g).s ≫ g = Abelian.image.ι g := by
  let s : Abelian.image g ⟶ X := (kernelImageSESSplitting g).s
  have hSection : s ≫ Abelian.factorThruImage g = 𝟙 (Abelian.image g) :=
    (kernelImageSESSplitting g).s_g
  exact (congrArg (fun t : X ⟶ Y => s ≫ t) (Abelian.image.fac g).symm).trans
    ((Category.assoc s (Abelian.factorThruImage g) (Abelian.image.ι g)).symm.trans
      ((congrArg (fun t : Abelian.image g ⟶ Abelian.image g => t ≫ Abelian.image.ι g)
        hSection).trans (Category.id_comp _)))

end CategoryTheory.Abelian
