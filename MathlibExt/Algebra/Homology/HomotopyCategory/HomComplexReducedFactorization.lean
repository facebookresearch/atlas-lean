/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Factorization of homogeneous cochains through a cokernel and kernel

Let D be preadditive with kernels and cokernels. For complex maps η : U → C and ε : A → V, any
homogeneous degree-n cochain θ : C → A with θ ∘ η=0 and ε ∘ θ=0 has a unique factor from coker η
to ker ε.

Conversely, reconstruction by the complex quotient and inclusion satisfies both vanishing
conditions. Neither the cochain nor its factor is required to commute with the differential.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [HasKernels D] [HasCokernels D]

private theorem factor_cokernel_kernel_component
    {U C A V : CochainComplex D ℤ} (η : U ⟶ C) (ε : A ⟶ V)
    [HasCokernel η] [HasKernel ε]
    (p q : ℤ) (f : C.X p ⟶ A.X q)
    (hpre : η.f p ≫ f = 0) (hpost : f ≫ ε.f q = 0) :
    ∃! θ : (cokernel η).X p ⟶ (kernel ε).X q,
      (cokernel.π η).f p ≫ θ ≫ (kernel.ι ε).f q = f := by
  let Eₚ := HomologicalComplex.eval D (ComplexShape.up ℤ) p
  let E_q := HomologicalComplex.eval D (ComplexShape.up ℤ) q
  let _ : PreservesColimit (parallelPair η 0) Eₚ :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f η p
  let _ : PreservesLimit (parallelPair ε 0) E_q :=
    HomologicalComplex.eval_preservesLimit_of_hasKernel_f ε q
  let S : CokernelCofork (η.f p) :=
    (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η)).map Eₚ
  let hS : IsColimit S :=
    CokernelCofork.mapIsColimit
      (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η))
      (cokernelIsCokernel η) Eₚ
  let T : KernelFork (ε.f q) :=
    (KernelFork.ofι (kernel.ι ε) (kernel.condition ε)).map E_q
  let hT : IsLimit T :=
    KernelFork.mapIsLimit
      (KernelFork.ofι (kernel.ι ε) (kernel.condition ε))
      (kernelIsKernel ε) E_q
  have hpre' : η.f p ≫ f = (0 : U.X p ⟶ C.X p) ≫ f := by
    simpa only [zero_comp] using hpre
  let γ : (cokernel η).X p ⟶ A.X q :=
    Cofork.IsColimit.desc hS f hpre'
  have hγ : (cokernel.π η).f p ≫ γ = f :=
    Cofork.IsColimit.π_desc' hS f hpre'
  have hγpost : γ ≫ ε.f q = 0 := by
    apply Cofork.IsColimit.hom_ext hS
    change (cokernel.π η).f p ≫ (γ ≫ ε.f q) = (cokernel.π η).f p ≫ 0
    rw [← Category.assoc, hγ, hpost, comp_zero]
  have hγpost' : γ ≫ ε.f q = γ ≫ (0 : A.X q ⟶ V.X q) := by
    simpa only [comp_zero] using hγpost
  let θ : (cokernel η).X p ⟶ (kernel ε).X q :=
    Fork.IsLimit.lift hT γ hγpost'
  have hθ : θ ≫ (kernel.ι ε).f q = γ :=
    Fork.IsLimit.lift_ι' hT γ hγpost'
  have hrecover : (cokernel.π η).f p ≫ θ ≫ (kernel.ι ε).f q = f := by
    rw [hθ, hγ]
  refine ⟨θ, hrecover, ?_⟩
  intro ψ hψ
  apply Fork.IsLimit.hom_ext hT
  apply Cofork.IsColimit.hom_ext hS
  change (cokernel.π η).f p ≫ (ψ ≫ (kernel.ι ε).f q) =
    (cokernel.π η).f p ≫ (θ ≫ (kernel.ι ε).f q)
  exact hψ.trans hrecover.symm

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. For every θ ∈ Annⁿ(η,ε), there exists a unique degree-n
cochain θ′ : coker η → ker ε with i_ε ∘ θ′ ∘ π_η=θ. The factor need not be a cocycle or a chain
map. -/
theorem exists_unique_factor_cokernel_kernel
    {U C A V : CochainComplex D ℤ} (η : U ⟶ C) (ε : A ⟶ V)
    (d : ℤ) (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0)
    (hpost : τ.comp (ofHom ε) (add_zero d) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∃! θ : Cochain (cokernel η) (kernel ε) d,
      ((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
        (ofHom (kernel.ι ε)) (add_zero d) = τ := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  have hpreComponent (p q : ℤ) (hpq : p + d = q) :
      η.f p ≫ τ.v p q hpq = 0 := by
    have h := congr_v hpre p q hpq
    simpa only [zero_cochain_comp_v, ofHom_v, zero_v] using h
  have hpostComponent (p q : ℤ) (hpq : p + d = q) :
      τ.v p q hpq ≫ ε.f q = 0 := by
    have h := congr_v hpost p q hpq
    simpa only [comp_zero_cochain_v, ofHom_v, zero_v] using h
  let θ : Cochain (cokernel η) (kernel ε) d :=
    Cochain.mk fun p q hpq =>
      Classical.choose (factor_cokernel_kernel_component η ε p q (τ.v p q hpq)
        (hpreComponent p q hpq) (hpostComponent p q hpq))
  have hcomponent (p q : ℤ) (hpq : p + d = q) :
      (cokernel.π η).f p ≫ θ.v p q hpq ≫ (kernel.ι ε).f q = τ.v p q hpq :=
    (Classical.choose_spec (factor_cokernel_kernel_component η ε p q (τ.v p q hpq)
      (hpreComponent p q hpq) (hpostComponent p q hpq))).1
  have hθ :
      ((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
        (ofHom (kernel.ι ε)) (add_zero d) = τ := by
    apply Cochain.ext
    intro p q hpq
    have hleft :
        ((cokernel.π η).f p ≫ θ.v p q hpq) ≫ (kernel.ι ε).f q = τ.v p q hpq :=
      (Category.assoc ((cokernel.π η).f p) (θ.v p q hpq) ((kernel.ι ε).f q)).trans
        (hcomponent p q hpq)
    simpa only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v] using hleft
  refine ⟨θ, hθ, ?_⟩
  intro ψ hψ
  apply Cochain.ext
  intro p q hpq
  have hψcomponent :
      (cokernel.π η).f p ≫ ψ.v p q hpq ≫ (kernel.ι ε).f q = τ.v p q hpq := by
    have h := congr_v hψ p q hpq
    have hleft :
        ((cokernel.π η).f p ≫ ψ.v p q hpq) ≫ (kernel.ι ε).f q = τ.v p q hpq := by
      simpa only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v] using h
    exact (Category.assoc ((cokernel.π η).f p) (ψ.v p q hpq)
      ((kernel.ι ε).f q)).symm.trans hleft
  exact (Classical.choose_spec (factor_cokernel_kernel_component η ε p q (τ.v p q hpq)
    (hpreComponent p q hpq) (hpostComponent p q hpq))).2 (ψ.v p q hpq) hψcomponent

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. For every degree-n cochain θ′ : coker η → ker ε, the
reconstruction θ=i_ε ∘ θ′ ∘ π_η satisfies θ ∘ η=0 and ε ∘ θ=0. -/
theorem reconstruction_cokernel_kernel_vanish
    {U C A V : CochainComplex D ℤ} (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∀ θ : Cochain (cokernel η) (kernel ε) d,
      (ofHom η).comp
          (((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
            (ofHom (kernel.ι ε)) (add_zero d)) (zero_add d) = 0 ∧
        (((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
          (ofHom (kernel.ι ε)) (add_zero d)).comp (ofHom ε) (add_zero d) = 0 := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  intro θ
  constructor
  · apply Cochain.ext
    intro p q hpq
    have hηp : η.f p ≫ (cokernel.π η).f p = 0 := by
      change (η ≫ cokernel.π η).f p = 0
      rw [cokernel.condition]
      rfl
    simp only [zero_cochain_comp_v, comp_zero_cochain_v, ofHom_v, zero_v]
    rw [← Category.assoc, ← Category.assoc, hηp, zero_comp, zero_comp]
  · apply Cochain.ext
    intro p q hpq
    have hεq : (kernel.ι ε).f q ≫ ε.f q = 0 := by
      change (kernel.ι ε ≫ ε).f q = 0
      rw [kernel.condition]
      rfl
    simp only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v, zero_v]
    rw [Category.assoc, hεq, comp_zero]

end CochainComplex.HomComplex.Cochain
