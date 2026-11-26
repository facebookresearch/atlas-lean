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
# The homology sequence of a coimage factorization

For a morphism f : K → L of complexes of arbitrary shape in an abelian category, the canonical
sequence ker(f) → K → coim(f) is short exact. Its connecting maps H_i(coim f) → H_j(ker f),
for c.Rel i j, give the adjacent exact homology segments.

If the canonical monomorphism coim(f) → L is a quasi-isomorphism, its homology isomorphism
transports the coimage terms and connecting maps to L. This yields the corresponding exact
sequence through H(K), H(L) and H(ker f), with that quasi-isomorphism hypothesis explicit.
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

/-- The kernel–source–coimage short complex.

For f : K → L, form ker(f) → K → coim(f) using the kernel inclusion and canonical coimage
projection. -/
noncomputable def coimageSequence (f : K ⟶ L) :
    ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
    (cokernel.condition (kernel.ι f))

/-- The first object of the coimage sequence.

The first term is the kernel complex of f. -/
@[simp]
theorem coimageSequence_X₁ (f : K ⟶ L) :
    (coimageSequence f).X₁ = kernel f :=
  rfl

/-- The middle object of the coimage sequence.

The middle term is the source complex K. -/
@[simp]
theorem coimageSequence_X₂ (f : K ⟶ L) :
    (coimageSequence f).X₂ = K :=
  rfl

/-- The last object of the coimage sequence.

The last term is the coimage complex of f. -/
@[simp]
theorem coimageSequence_X₃ (f : K ⟶ L) :
    (coimageSequence f).X₃ = Abelian.coimage f :=
  rfl

/-- The first map of the coimage sequence.

The first arrow is kernel.ι f. -/
@[simp]
theorem coimageSequence_f (f : K ⟶ L) :
    (coimageSequence f).f = kernel.ι f :=
  rfl

/-- The last map of the coimage sequence.

The last arrow is the canonical projection K → coim(f). -/
@[simp]
theorem coimageSequence_g (f : K ⟶ L) :
    (coimageSequence f).g = Abelian.coimage.π f :=
  rfl

/-- Short exactness of the coimage sequence.

For every complex morphism f, ker(f) → K → coim(f) is short exact. -/
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

/-- The kernel inclusion is killed by the coimage projection.

The composite ker(f) → K → coim(f) is zero. -/
@[reassoc]
theorem kernel_ι_comp_coimage_π (f : K ⟶ L) :
    kernel.ι f ≫ Abelian.coimage.π f = 0 := by
  exact cokernel.condition _

/-- The connecting map from coimage to kernel homology.

For c.Rel i j, the short exact coimage sequence gives δ : H_i(coim f) → H_j(ker f). -/
noncomputable def coimageBoundary (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (Abelian.coimage f).homology i ⟶ (kernel f).homology j :=
  (coimageSequence_shortExact f).δ i j hij

/-- The coimage connecting map is killed by kernel inclusion on homology.

The composite δ followed by H_j(ker f) → H_j(K) is zero. -/
@[reassoc (attr := simp)]
theorem coimageBoundary_comp_kernelHomologyMap (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    coimageBoundary f i j hij ≫ homologyMap (kernel.ι f) j = 0 := by
  change (coimageSequence_shortExact f).δ i j hij ≫
    homologyMap (kernel.ι f) j = 0
  exact (coimageSequence_shortExact f).δ_comp i j hij

/-- The coimage projection on homology is killed by the connecting map.

The composite H_i(K) → H_i(coim f) → H_j(ker f) is zero. -/
@[reassoc (attr := simp)]
theorem homologyMap_coimage_π_comp_coimageBoundary (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    homologyMap (Abelian.coimage.π f) i ≫
        coimageBoundary f i j hij = 0 := by
  change homologyMap (coimageSequence f).g i ≫
      (coimageSequence_shortExact f).δ i j hij = 0
  exact (coimageSequence_shortExact f).comp_δ i j hij

/-- Exactness at source homology in the coimage sequence.

The segment H_i(ker f) → H_i(K) → H_i(coim f) is exact. -/
theorem coimageSequence_homology_exact_source (f : K ⟶ L) (i : ι) :
    (ShortComplex.mk (homologyMap (kernel.ι f) i)
      (homologyMap (Abelian.coimage.π f) i)
      (by
        rw [← homologyMap_comp, kernel_ι_comp_coimage_π,
          homologyMap_zero])).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g] using
      (coimageSequence_shortExact f).homology_exact₂ i

/-- Exactness at kernel homology in the coimage sequence.

For c.Rel i j, the segment H_i(coim f) → H_j(ker f) → H_j(K) is exact. -/
theorem coimageSequence_homology_exact_kernel (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (coimageBoundary f i j hij)
      (homologyMap (kernel.ι f) j)
      ((coimageSequence_shortExact f).δ_comp i j hij)).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g,
    coimageBoundary] using
      (coimageSequence_shortExact f).homology_exact₁ i j hij

/-- Exactness at coimage homology in the coimage sequence.

For c.Rel i j, the segment H_i(K) → H_i(coim f) → H_j(ker f) is exact. -/
theorem coimageSequence_homology_exact_coimage (f : K ⟶ L)
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (homologyMap (Abelian.coimage.π f) i)
      (coimageBoundary f i j hij)
      (homologyMap_coimage_π_comp_coimageBoundary f i j hij)).Exact := by
  simpa only [coimageSequence_X₁, coimageSequence_X₂,
    coimageSequence_X₃, coimageSequence_f, coimageSequence_g,
    coimageBoundary] using
      (coimageSequence_shortExact f).homology_exact₃ i j hij

/-- The coimage-to-target homology isomorphism under a quasi-isomorphism.

If coim(f) → L is a quasi-isomorphism, its degree-i homology map gives H_i(coim f) ≅ H_i(L). -/
noncomputable def coimageHomologyIsoTarget (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f)) (i : ι) :
    (Abelian.coimage f).homology i ≅ L.homology i := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  exact isoOfQuasiIsoAt (Abelian.factorThruCoimage f) i

/-- The map of the coimage-to-target homology comparison.

The forward comparison is the homology map of the canonical factorThruCoimage morphism. -/
@[simp]
theorem coimageHomologyIsoTarget_hom (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f)) (i : ι) :
    (coimageHomologyIsoTarget f h i).hom =
      homologyMap (Abelian.factorThruCoimage f) i := by
  let _ : QuasiIso (Abelian.factorThruCoimage f) := h
  rfl

/-- The connecting map with the coimage term transported to the target.

Under the stated quasi-isomorphism, precompose the coimage connecting map with H_i(L) →
H_i(coim f). -/
noncomputable def coimageTargetBoundary (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    L.homology i ⟶ (kernel f).homology j :=
  (coimageHomologyIsoTarget f h i).inv ≫ coimageBoundary f i j hij

/-- The transported target boundary is killed by source inclusion.

Under the coimage-to-target quasi-isomorphism, the composite H_i(L) → H_j(ker f) → H_j(K) is
zero. -/
@[reassoc (attr := simp)]
theorem coimageTargetBoundary_comp_kernelHomologyMap (f : K ⟶ L)
    (h : QuasiIso (Abelian.factorThruCoimage f))
    (i j : ι) (hij : c.Rel i j) :
    coimageTargetBoundary f h i j hij ≫ homologyMap (kernel.ι f) j = 0 := by
  dsimp [coimageTargetBoundary]
  rw [Category.assoc, coimageBoundary_comp_kernelHomologyMap,
    comp_zero]

/-- The original morphism on homology is killed by the transported boundary.

Under the coimage-to-target quasi-isomorphism, H_i(f) followed by the target boundary is zero. -/
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

/-- Exactness at source homology after target transport.

If coim(f) → L is a quasi-isomorphism, H_i(ker f) → H_i(K) → H_i(L) is exact. -/
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

/-- Exactness at kernel homology after target transport.

Under the coimage-to-target quasi-isomorphism, H_i(L) → H_j(ker f) → H_j(K) is exact for c.Rel
i j. -/
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

/-- Exactness at target homology after coimage transport.

Under the coimage-to-target quasi-isomorphism, H_i(K) → H_i(L) → H_j(ker f) is exact for c.Rel
i j. -/
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
