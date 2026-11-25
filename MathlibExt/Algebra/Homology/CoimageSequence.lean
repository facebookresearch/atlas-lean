/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology localization through the coimage of a chain map

For an arbitrary morphism of homological complexes in an abelian category,
this file packages the canonical short exact sequence from its kernel to its
source to its coimage.  It exposes the associated connecting morphism and
exact homology segments.  If the canonical coimage-to-target monomorphism is
a quasi-isomorphism, it transports the sequence to the target complex.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι}
variable {K L : HomologicalComplex C c}

/-- The canonical kernel--source--coimage short complex of a chain map. -/
noncomputable def coimageSequence (f : K ⟶ L) :
    ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
    (cokernel.condition (kernel.ι f))

@[simp]
theorem coimageSequence_X₁ (f : K ⟶ L) :
    (coimageSequence f).X₁ = kernel f :=
  rfl

@[simp]
theorem coimageSequence_X₂ (f : K ⟶ L) :
    (coimageSequence f).X₂ = K :=
  rfl

@[simp]
theorem coimageSequence_X₃ (f : K ⟶ L) :
    (coimageSequence f).X₃ = Abelian.coimage f :=
  rfl

@[simp]
theorem coimageSequence_f (f : K ⟶ L) :
    (coimageSequence f).f = kernel.ι f :=
  rfl

@[simp]
theorem coimageSequence_g (f : K ⟶ L) :
    (coimageSequence f).g = Abelian.coimage.π f :=
  rfl

/-- The kernel--source--coimage sequence is short exact. -/
theorem coimageSequence_shortExact (f : K ⟶ L) :
    (coimageSequence f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (cokernelIsCokernel (kernel.ι f))
  mono_f := by
    change Mono (kernel.ι f)
    infer_instance
  epi_g := by
    dsimp [coimageSequence]
    infer_instance

@[reassoc]
theorem kernel_ι_comp_coimage_π (f : K ⟶ L) :
    kernel.ι f ≫ Abelian.coimage.π f = 0 := by
  exact cokernel.condition _

/-- Connecting morphism from coimage homology to kernel homology. -/
noncomputable def coimageBoundary (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (Abelian.coimage f).homology i ⟶ (kernel f).homology j :=
  (coimageSequence_shortExact f).δ i j hij

@[reassoc (attr := simp)]
theorem coimageBoundary_comp_kernelHomologyMap (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    coimageBoundary f i j hij ≫ homologyMap (kernel.ι f) j = 0 := by
  change (coimageSequence_shortExact f).δ i j hij ≫
    homologyMap (kernel.ι f) j = 0
  exact (coimageSequence_shortExact f).δ_comp i j hij

@[reassoc (attr := simp)]
theorem homologyMap_coimage_π_comp_coimageBoundary (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    homologyMap (Abelian.coimage.π f) i ≫
        coimageBoundary f i j hij = 0 := by
  change homologyMap (coimageSequence f).g i ≫
      (coimageSequence_shortExact f).δ i j hij = 0
  exact (coimageSequence_shortExact f).comp_δ i j hij

/-- Exactness at source homology in the kernel--source--coimage sequence. -/
theorem coimageSequence_homology_exact_source (f : K ⟶ L) (i : ι) :
    (ShortComplex.mk (homologyMap (kernel.ι f) i)
      (homologyMap (Abelian.coimage.π f) i)
      (by
        rw [← homologyMap_comp, kernel_ι_comp_coimage_π,
          homologyMap_zero])).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g] using
      (coimageSequence_shortExact f).homology_exact₂ i

/-- Exactness at kernel homology in the kernel--source--coimage sequence. -/
theorem coimageSequence_homology_exact_kernel (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (coimageBoundary f i j hij)
      (homologyMap (kernel.ι f) j)
      ((coimageSequence_shortExact f).δ_comp i j hij)).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g,
    coimageBoundary] using
      (coimageSequence_shortExact f).homology_exact₁ i j hij

/-- Exactness at coimage homology in the kernel--source--coimage sequence. -/
theorem coimageSequence_homology_exact_coimage (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (homologyMap (Abelian.coimage.π f) i)
      (coimageBoundary f i j hij)
      (homologyMap_coimage_π_comp_coimageBoundary f i j hij)).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g,
    coimageBoundary] using
      (coimageSequence_shortExact f).homology_exact₃ i j hij

/-- A quasi-isomorphism from the coimage of a chain map to its target
induces the canonical homology isomorphism. -/
noncomputable def coimageHomologyIsoTarget (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f)) (i : ι) :
    (Abelian.coimage f).homology i ≅ L.homology i := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  exact isoOfQuasiIsoAt (Abelian.factorThruCoimage f) i

@[simp]
theorem coimageHomologyIsoTarget_hom (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f)) (i : ι) :
    (coimageHomologyIsoTarget f h i).hom =
      homologyMap (Abelian.factorThruCoimage f) i := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  rfl

/-- Connecting morphism with the coimage homology term transported to the
target of the original chain map. -/
noncomputable def coimageTargetBoundary (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    L.homology i ⟶ (kernel f).homology j :=
  (coimageHomologyIsoTarget f h i).inv ≫ coimageBoundary f i j hij

@[reassoc (attr := simp)]
theorem coimageTargetBoundary_comp_kernelHomologyMap (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    coimageTargetBoundary f h i j hij ≫ homologyMap (kernel.ι f) j = 0 := by
  dsimp [coimageTargetBoundary]
  rw [Category.assoc, coimageBoundary_comp_kernelHomologyMap,
    comp_zero]

@[reassoc (attr := simp)]
theorem homologyMap_comp_coimageTargetBoundary (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    homologyMap f i ≫ coimageTargetBoundary f h i j hij = 0 := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  dsimp [coimageTargetBoundary]
  have hfac : homologyMap f i =
      homologyMap (Abelian.coimage.π f) i ≫
        (coimageHomologyIsoTarget f h i).hom := by
    rw [coimageHomologyIsoTarget_hom, ← homologyMap_comp,
      Abelian.coimage.fac]
  rw [hfac, Category.assoc, Iso.hom_inv_id_assoc,
    homologyMap_coimage_π_comp_coimageBoundary]

/-- If coimage-to-target is a quasi-isomorphism, the
kernel-to-source-to-target homology segment is exact at source homology. -/
theorem coimageTarget_homology_exact_source (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f)) (i : ι) :
    (ShortComplex.mk (homologyMap (kernel.ι f) i) (homologyMap f i)
      (by
        rw [← homologyMap_comp, kernel.condition, homologyMap_zero])).Exact := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  let S₁ := ShortComplex.mk (homologyMap (kernel.ι f) i)
    (homologyMap (Abelian.coimage.π f) i)
    (by
      rw [← homologyMap_comp, kernel_ι_comp_coimage_π,
        homologyMap_zero])
  let S₂ := ShortComplex.mk (homologyMap (kernel.ι f) i)
    (homologyMap f i)
    (by rw [← homologyMap_comp, kernel.condition, homologyMap_zero])
  let e : S₁ ≅ S₂ := ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (coimageHomologyIsoTarget f h i) (by
      dsimp [S₁, S₂]
      simp only [Category.id_comp, Category.comp_id]) (by
      dsimp [S₁, S₂]
      rw [Category.id_comp, coimageHomologyIsoTarget_hom,
        ← homologyMap_comp, Abelian.coimage.fac])
  have hS₂ : S₂.Exact := ShortComplex.exact_of_iso e
    (coimageSequence_homology_exact_source f i)
  simpa only [S₂] using hS₂

/-- If coimage-to-target is a quasi-isomorphism, the
target-to-kernel-to-source homology segment is exact at kernel homology. -/
theorem coimageTarget_homology_exact_kernel (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (coimageTargetBoundary f h i j hij)
      (homologyMap (kernel.ι f) j)
      (coimageTargetBoundary_comp_kernelHomologyMap f h i j hij)).Exact := by
  let S₁ := ShortComplex.mk (coimageBoundary f i j hij)
    (homologyMap (kernel.ι f) j)
    ((coimageSequence_shortExact f).δ_comp i j hij)
  let S₂ := ShortComplex.mk (coimageTargetBoundary f h i j hij)
    (homologyMap (kernel.ι f) j)
    (coimageTargetBoundary_comp_kernelHomologyMap f h i j hij)
  let e : S₁ ≅ S₂ := ShortComplex.isoMk
    (coimageHomologyIsoTarget f h i) (Iso.refl _) (Iso.refl _) (by
      dsimp [S₁, S₂, coimageTargetBoundary]
      rw [Iso.hom_inv_id_assoc, Category.comp_id]) (by
        dsimp [S₁, S₂]
        simp only [Category.id_comp, Category.comp_id])
  have hS₂ : S₂.Exact := ShortComplex.exact_of_iso e
    (coimageSequence_homology_exact_kernel f i j hij)
  simpa only [S₂] using hS₂

/-- If coimage-to-target is a quasi-isomorphism, the
source-to-target-to-kernel homology segment is exact at target homology. -/
theorem coimageTarget_homology_exact_target (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (homologyMap f i)
      (coimageTargetBoundary f h i j hij)
      (homologyMap_comp_coimageTargetBoundary f h i j hij)).Exact := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  let S₁ := ShortComplex.mk (homologyMap (Abelian.coimage.π f) i)
    (coimageBoundary f i j hij)
    (homologyMap_coimage_π_comp_coimageBoundary f i j hij)
  let S₂ := ShortComplex.mk (homologyMap f i)
    (coimageTargetBoundary f h i j hij)
    (homologyMap_comp_coimageTargetBoundary f h i j hij)
  let e : S₁ ≅ S₂ := ShortComplex.isoMk (Iso.refl _)
    (coimageHomologyIsoTarget f h i) (Iso.refl _) (by
      dsimp [S₁, S₂]
      rw [Category.id_comp, coimageHomologyIsoTarget_hom, ← homologyMap_comp,
        Abelian.coimage.fac]) (by
      dsimp [S₁, S₂, coimageTargetBoundary]
      rw [Category.comp_id, Iso.hom_inv_id_assoc])
  have hS₂ : S₂.Exact := ShortComplex.exact_of_iso e
    (coimageSequence_homology_exact_coimage f i j hij)
  simpa only [S₂] using hS₂

end HomologicalComplex
