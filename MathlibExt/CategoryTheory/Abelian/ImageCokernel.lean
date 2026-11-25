/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Cokernels of image and coimage factorizations

A morphism and its image inclusion have canonically isomorphic cokernels.
The isomorphism preserves the quotient projections and is natural in
commutative arrow squares. The coimage presentation uses the canonical
coimage-to-image isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {X Y : C} (f : X ⟶ Y)

/-- Quotient by the image is the cokernel of the morphism. -/
def imageCokernelIso : cokernel (image.ι f) ≅ cokernel f :=
  colimit.isoColimitCocone
    ⟨_, epiIsCokernelOfKernel (f := cokernel.π f)
      (KernelFork.ofι (image.ι f) (kernel.condition (cokernel.π f)))
      (kernelIsKernel (cokernel.π f))⟩

/-- The image-quotient comparison retains the cokernel projection. -/
@[reassoc (attr := simp)]
theorem imageCokernelIso_projection :
    cokernel.π (image.ι f) ≫ (imageCokernelIso f).hom = cokernel.π f :=
  colimit.isoColimitCocone_ι_hom _ WalkingParallelPair.one

/-- Its inverse retains that same quotient projection. -/
@[reassoc (attr := simp)]
theorem imageCokernelIso_projection_inv :
    cokernel.π f ≫ (imageCokernelIso f).inv = cokernel.π (image.ι f) :=
  colimit.isoColimitCocone_ι_inv
    ⟨_, epiIsCokernelOfKernel (f := cokernel.π f)
      (KernelFork.ofι (image.ι f) (kernel.condition (cokernel.π f)))
      (kernelIsKernel (cokernel.π f))⟩ WalkingParallelPair.one

/-- Descend an map annihilating the morphism through its image quotient. -/
def imageCokernelDesc {T : C} (g : Y ⟶ T) (hg : f ≫ g = 0) :
    cokernel (image.ι f) ⟶ T :=
  cokernel.desc (image.ι f) g (image_ι_comp_eq_zero hg)

/-- The universal descent is characterized by the quotient square. -/
@[reassoc (attr := simp)]
theorem imageCokernelDesc_projection {T : C} (g : Y ⟶ T) (hg : f ≫ g = 0) :
    cokernel.π (image.ι f) ≫ imageCokernelDesc f g hg = g :=
  cokernel.π_desc _ _ _

/-- The projection determines the universal descent. -/
theorem imageCokernelDesc_unique {T : C} (g : Y ⟶ T) (hg : f ≫ g = 0)
    (l : cokernel (image.ι f) ⟶ T) (hl : cokernel.π (image.ι f) ≫ l = g) :
    l = imageCokernelDesc f g hg := by
  apply (cancel_epi (cokernel.π (image.ι f))).1
  exact hl.trans (imageCokernelDesc_projection f g hg).symm

section Naturality

variable {X' Y' : C} {g : X' ⟶ Y'} (a : Arrow.mk f ⟶ Arrow.mk g)

/-- The image map retains the target side of the arrow square. -/
theorem imageCokernelSquare :
    image.ι f ≫ a.right = (im (C := C)).map a ≫ image.ι g := by
  exact (kernel.lift_ι (cokernel.π g) (image.ι f ≫ a.right) _).symm

/-- An square induces the map between its image quotients. -/
def imageCokernelMap : cokernel (image.ι f) ⟶ cokernel (image.ι g) :=
  cokernel.map (image.ι f) (image.ι g) ((im (C := C)).map a) a.right
    (imageCokernelSquare f a)

/-- The image-quotient map retains the target side of the square. -/
@[reassoc (attr := simp)]
theorem imageCokernelMap_projection :
    cokernel.π (image.ι f) ≫ imageCokernelMap f a =
      a.right ≫ cokernel.π (image.ι g) :=
  cokernel.π_desc _ _ _

/-- Image-quotient and cokernel maps commute with the comparison. -/
@[reassoc]
theorem imageCokernelIso_naturality :
    imageCokernelMap f a ≫ (imageCokernelIso g).hom =
      (imageCokernelIso f).hom ≫ cokernel.map f g a.left a.right a.w.symm := by
  apply (cancel_epi (cokernel.π (image.ι f))).1
  rw [← Category.assoc, imageCokernelMap_projection, Category.assoc,
    imageCokernelIso_projection, ← Category.assoc, imageCokernelIso_projection]
  exact (cokernel.π_desc _ _ _).symm

/-- The quotient descent is natural in the square and its target map. -/
@[reassoc]
theorem imageCokernelMap_desc {T T' : C} (b : Y ⟶ T) (b' : Y' ⟶ T')
    (hb : f ≫ b = 0) (hb' : g ≫ b' = 0) (t : T ⟶ T')
    (ht : a.right ≫ b' = b ≫ t) :
    imageCokernelMap f a ≫ imageCokernelDesc g b' hb' =
      imageCokernelDesc f b hb ≫ t := by
  apply (cancel_epi (cokernel.π (image.ι f))).1
  rw [← Category.assoc, imageCokernelMap_projection, Category.assoc,
    imageCokernelDesc_projection, ← Category.assoc, imageCokernelDesc_projection]
  exact ht

end Naturality

/-- Quotient by the image is functorial in every arrow square. -/
def imageCokernelFunctor : Arrow C ⥤ C where
  obj a := cokernel (image.ι a.hom)
  map {a b} f := imageCokernelMap a.hom f
  map_id a := by
    rcases a with ⟨X, Y, h⟩
    apply (cancel_epi (cokernel.π (image.ι h))).1
    rw [imageCokernelMap_projection]
    exact (congrArg
      (fun k : Y ⟶ Y => k ≫ cokernel.π (image.ι h))
      (Arrow.id_right (Arrow.mk h))).trans
        ((Category.id_comp (cokernel.π (image.ι h))).trans
          (Category.comp_id (cokernel.π (image.ι h))).symm)
  map_comp {a b c} f g := by
    rcases a with ⟨X₁, Y₁, h₁⟩
    rcases b with ⟨X₂, Y₂, h₂⟩
    rcases c with ⟨X₃, Y₃, h₃⟩
    apply (cancel_epi (cokernel.π (image.ι h₁))).1
    rw [imageCokernelMap_projection, ← Category.assoc, imageCokernelMap_projection,
      Category.assoc, imageCokernelMap_projection]
    exact (congrArg
      (fun k : Y₁ ⟶ Y₃ => k ≫ cokernel.π (image.ι h₃))
      (Arrow.comp_right f g)).trans (Category.assoc f.right g.right _)

/-- The target-to-image-quotient projection is natural in arrow maps. -/
def imageCokernelProjection : (Arrow.rightFunc : Arrow C ⥤ C) ⟶ imageCokernelFunctor where
  app a := cokernel.π (image.ι a.hom)
  naturality {a b} f := (imageCokernelMap_projection a.hom f).symm

/-- The coimage presentation gives the same cokernel. -/
def coimageCokernelIso : cokernel (Abelian.factorThruCoimage f) ≅ cokernel f :=
  cokernel.mapIso (Abelian.factorThruCoimage f) (image.ι f)
      (coimageIsoImage f) (Iso.refl Y) (by
        apply (cancel_epi (coimage.π f)).1
        calc
          coimage.π f ≫ Abelian.factorThruCoimage f ≫ (Iso.refl Y).hom = f := by
            rw [← Category.assoc, coimage.fac]
            exact Category.comp_id f
          _ = coimage.π f ≫ (coimageIsoImage f).hom ≫ image.ι f := by
            simpa only [coimageIsoImage, asIso_hom] using
              (coimage_image_factorisation f).symm) ≪≫
    imageCokernelIso f

/-- The coimage comparison also retains the projection. -/
@[reassoc]
theorem coimageCokernelIso_projection :
    cokernel.π (Abelian.factorThruCoimage f) ≫ (coimageCokernelIso f).hom = cokernel.π f := by
  simp only [coimageCokernelIso, Iso.trans_hom, cokernel.mapIso_hom]
  rw [← Category.assoc, cokernel.π_desc]
  simpa only [Iso.refl_hom, Category.id_comp] using imageCokernelIso_projection f

section CoimageNaturality

variable {X' Y' : C} {g : X' ⟶ Y'} (a : Arrow.mk f ⟶ Arrow.mk g)

/-- The coimage map retains the target side of the arrow square. -/
theorem coimageCokernelSquare :
    Abelian.factorThruCoimage f ≫ a.right = (coim (C := C)).map a ≫ Abelian.factorThruCoimage g := by
  let m : Abelian.coimage f ⟶ Abelian.coimage g := (coim (C := C)).map a
  have hπ : coimage.π f ≫ m = a.left ≫ coimage.π g := by
    dsimp only [m]
    rw [coim_map]
    exact cokernel.π_desc _ _ _
  apply (cancel_epi (coimage.π f)).1
  calc
    coimage.π f ≫ (Abelian.factorThruCoimage f ≫ a.right) =
        (coimage.π f ≫ Abelian.factorThruCoimage f) ≫ a.right :=
      (Category.assoc (coimage.π f) (Abelian.factorThruCoimage f) a.right).symm
    _ = f ≫ a.right :=
      congrArg (fun k : X ⟶ Y => k ≫ a.right) (coimage.fac f)
    _ = a.left ≫ g := a.w.symm
    _ = a.left ≫ (coimage.π g ≫ Abelian.factorThruCoimage g) :=
      congrArg (fun k : X' ⟶ Y' => a.left ≫ k) (coimage.fac g).symm
    _ = (a.left ≫ coimage.π g) ≫ Abelian.factorThruCoimage g :=
      (Category.assoc a.left (coimage.π g) (Abelian.factorThruCoimage g)).symm
    _ = (coimage.π f ≫ m) ≫ Abelian.factorThruCoimage g :=
      congrArg (fun k : X ⟶ Abelian.coimage g => k ≫ Abelian.factorThruCoimage g) hπ.symm
    _ = coimage.π f ≫ (m ≫ Abelian.factorThruCoimage g) :=
      Category.assoc (coimage.π f) m (Abelian.factorThruCoimage g)

/-- The coimage map of an square induces its quotient map. -/
def coimageCokernelMap : cokernel (Abelian.factorThruCoimage f) ⟶ cokernel (Abelian.factorThruCoimage g) :=
  cokernel.map (Abelian.factorThruCoimage f) (Abelian.factorThruCoimage g)
    ((coim (C := C)).map a) a.right (coimageCokernelSquare f a)

/-- The coimage quotient map retains the target side of the square. -/
@[reassoc (attr := simp)]
theorem coimageCokernelMap_projection :
    cokernel.π (Abelian.factorThruCoimage f) ≫ coimageCokernelMap f a =
      a.right ≫ cokernel.π (Abelian.factorThruCoimage g) :=
  cokernel.π_desc _ _ _

/-- The coimage presentation comparison is natural in arrow maps. -/
@[reassoc]
theorem coimageCokernelIso_naturality :
    coimageCokernelMap f a ≫ (coimageCokernelIso g).hom =
      (coimageCokernelIso f).hom ≫ cokernel.map f g a.left a.right a.w.symm := by
  apply (cancel_epi (cokernel.π (Abelian.factorThruCoimage f))).1
  rw [← Category.assoc, coimageCokernelMap_projection, Category.assoc,
    coimageCokernelIso_projection, ← Category.assoc, coimageCokernelIso_projection]
  exact (cokernel.π_desc _ _ _).symm

end CoimageNaturality

end CategoryTheory.Abelian

end
