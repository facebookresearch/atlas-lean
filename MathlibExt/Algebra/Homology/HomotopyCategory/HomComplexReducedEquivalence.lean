/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexReducedFactorization
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# A quotient and kernel description of homogeneous cochains

Let D be preadditive, η : U → C and ε : A → V maps of integer cochain complexes. The degree-n
cochains θ : C → A with θ ∘ η=0 and ε ∘ θ=0 form the two-sided annihilator additive subgroup.

If D has kernels and cokernels, every such cochain factors uniquely as C → coker(η) → ker(ε) →
A. Reconstruction through the cokernel quotient and kernel inclusion is an additive equivalence.
No cocycle condition or splitting is required.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {U C A V : CochainComplex D ℤ}

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. These cochains form an additive subgroup of Homⁿ(C,A), without a
kernel or cokernel assumption on D. -/
def annihilator (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) : AddSubgroup (Cochain C A d) where
  carrier := {τ | (ofHom η).comp τ (zero_add d) = 0 ∧
    τ.comp (ofHom ε) (add_zero d) = 0}
  zero_mem' := ⟨Cochain.comp_zero (ofHom η) (zero_add d),
    Cochain.zero_comp (ofHom ε) (add_zero d)⟩
  add_mem' := by
    intro τ σ hτ hσ
    constructor
    · simp only [Cochain.comp_add, hτ.1, hσ.1, add_zero]
    · simp only [Cochain.add_comp, hτ.2, hσ.2, add_zero]
  neg_mem' := by
    intro τ hτ
    constructor
    · simp only [Cochain.comp_neg, hτ.1, neg_zero]
    · simp only [Cochain.neg_comp, hτ.2, neg_zero]

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Membership θ ∈ Annⁿ(η,ε) is equivalent to the conjunction θ ∘
η=0 and ε ∘ θ=0, as equalities of homogeneous degree-n cochains. -/
@[simp]
theorem mem_annihilator (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) (τ : Cochain C A d) :
    τ ∈ annihilator η ε d ↔
      (ofHom η).comp τ (zero_add d) = 0 ∧ τ.comp (ofHom ε) (add_zero d) = 0 :=
  Iff.rfl

variable [HasKernels D] [HasCokernels D]

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. Reconstruction θ′ ↦ i_ε ∘ θ′ ∘ π_η gives an additive
equivalence Homⁿ(coker η,ker ε) ≅ Annⁿ(η,ε). Its inverse is the unique homogeneous factor, with
no cocycle hypothesis. -/
noncomputable def cokernelKernelAddEquiv (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    Cochain (cokernel η) (kernel ε) d ≃+ ↥(annihilator η ε d) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  change Cochain (cokernel η) (kernel ε) d ≃+ ↥(annihilator η ε d)
  let f : Cochain (cokernel η) (kernel ε) d →+ ↥(annihilator η ε d) :=
    { toFun θ :=
        ⟨((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
          (ofHom (kernel.ι ε)) (add_zero d),
          reconstruction_cokernel_kernel_vanish η ε d θ⟩
      map_zero' := by
        apply Subtype.ext
        change ((ofHom (cokernel.π η)).comp 0 (zero_add d)).comp
          (ofHom (kernel.ι ε)) (add_zero d) = 0
        simp only [Cochain.comp_zero, Cochain.zero_comp]
      map_add' θ ψ := by
        apply Subtype.ext
        change ((ofHom (cokernel.π η)).comp (θ + ψ) (zero_add d)).comp
            (ofHom (kernel.ι ε)) (add_zero d) =
          ((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
              (ofHom (kernel.ι ε)) (add_zero d) +
            ((ofHom (cokernel.π η)).comp ψ (zero_add d)).comp
              (ofHom (kernel.ι ε)) (add_zero d)
        simp only [Cochain.comp_add, Cochain.add_comp] }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro θ ψ h
    have hval := congrArg Subtype.val h
    obtain ⟨ρ, _, huniq⟩ := exists_unique_factor_cokernel_kernel η ε d
      (f θ).val (f θ).property.1 (f θ).property.2
    exact (huniq θ rfl).trans (huniq ψ hval.symm).symm
  · intro τ
    obtain ⟨θ, hθ, _⟩ := exists_unique_factor_cokernel_kernel η ε d
      τ.val τ.property.1 τ.property.2
    exact ⟨θ, Subtype.ext hθ⟩

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. For θ′ of degree n from coker η to ker ε, the corresponding
annihilator cochain is i_ε ∘ θ′ ∘ π_η, where π_η and i_ε are the complex cokernel quotient and
kernel inclusion. -/
theorem cokernelKernelAddEquiv_apply (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∀ θ : Cochain (cokernel η) (kernel ε) d,
      ((cokernelKernelAddEquiv η ε d) θ : Cochain C A d) =
        ((ofHom (cokernel.π η)).comp θ (zero_add d)).comp
          (ofHom (kernel.ι ε)) (add_zero d) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  intro θ
  rfl

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. For θ ∈ Annⁿ(η,ε), the inverse equivalence gives θ′ : coker
η → ker ε of degree n satisfying i_ε ∘ θ′ ∘ π_η=θ. -/
theorem cokernelKernelAddEquiv_symm_reconstruct (η : U ⟶ C) (ε : A ⟶ V) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∀ τ : annihilator η ε d,
      ((ofHom (cokernel.π η)).comp ((cokernelKernelAddEquiv η ε d).symm τ)
        (zero_add d)).comp (ofHom (kernel.ι ε)) (add_zero d) = (τ : Cochain C A d) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  intro τ
  have h := congrArg Subtype.val ((cokernelKernelAddEquiv η ε d).apply_symm_apply τ)
  exact (cokernelKernelAddEquiv_apply η ε d
    ((cokernelKernelAddEquiv η ε d).symm τ)).symm.trans h

end CochainComplex.HomComplex.Cochain
