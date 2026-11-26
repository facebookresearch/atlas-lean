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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulPredualQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Normal-map range as the annihilator of a predual kernel

For an injective normal unital complex star homomorphism `f : M → N`, let `B : N_* → M_*`,
`B(φ)=φ∘f`, be its predual pullback. An element `y ∈ N` belongs to `range f` exactly when
`φ(y)=0` for every `φ ∈ ker B`.

Thus annihilation of the predual kernel produces a source preimage. No prior range-closedness or
inverse map is a premise.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Operator preimage from annihilating the predual kernel.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Let `B=f.predualPullback : N_* → M_*`,
`B(φ)=φ∘f`, and `B*(F)=F∘B`. if `y ∈ N` satisfies `φ(y)=0` for every `φ ∈ N_*` with
`B(φ)=0`, then there exists `x ∈ M` with `f(x)=y`. -/
theorem exists_preimage_of_predual_kernel (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (y : N)
    (hy : ∀ φ : normalFunctionalSpace N, f.predualPullback φ = 0 → (φ : StrongDual ℂ N) y = 0) :
    ∃ x : M, f x = y := by
  let B := f.predualPullback
  let F : StrongDual ℂ (normalFunctionalSpace N) := normalFunctionalEvaluationEquiv N y
  have hsurj : Function.Surjective B := f.predualPullback_surjective_of_injective hf
  have hker : LinearMap.ker B.toLinearMap ≤ LinearMap.ker F.toLinearMap := by
    intro φ hφ
    change F φ = 0
    exact hy φ hφ
  let g : normalFunctionalSpace M →ₗ[ℂ] ℂ :=
    (B.toLinearMap.liftOfSurjective hsurj) ⟨F.toLinearMap, hker⟩
  have hvalue (φ : normalFunctionalSpace N) : g (B φ) = F φ :=
    LinearMap.equivOfSurjective_apply hsurj hker
  have hcontinuous : Continuous g := by
    apply (f.predualPullback_isQuotientMap_of_injective hf).continuous_iff.mpr
    have hfunction : ((g : normalFunctionalSpace M → ℂ) ∘ B) = F := funext hvalue
    rw [hfunction]
    exact F.continuous
  let G : StrongDual ℂ (normalFunctionalSpace M) := ⟨g, hcontinuous⟩
  let x : M := (normalFunctionalEvaluationEquiv M).symm G
  refine ⟨x, ?_⟩
  apply (normalFunctionalEvaluationEquiv N).injective
  apply ContinuousLinearMap.ext
  intro φ
  have hx : normalFunctionalEvaluationEquiv M x = G :=
    (normalFunctionalEvaluationEquiv M).apply_symm_apply G
  have hxeval := congrArg (fun L : StrongDual ℂ (normalFunctionalSpace M) => L (B φ)) hx
  calc
    normalFunctionalEvaluationEquiv N (f x) φ = (φ : StrongDual ℂ N) (f x) := rfl
    _ = (B φ : StrongDual ℂ M) x := (f.predualPullback_apply φ x).symm
    _ = G (B φ) := hxeval
    _ = F φ := hvalue φ
    _ = normalFunctionalEvaluationEquiv N y φ := rfl

/-- **Range membership exactly by predual-kernel annihilation.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Let `B=f.predualPullback : N_* → M_*`,
`B(φ)=φ∘f`, and `B*(F)=F∘B`. for `y ∈ N`, `y∈range f` if and only if `φ(y)=0` whenever `φ
∈ N_*` and `B(φ)=0`. -/
theorem mem_range_iff_predual_kernel (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (y : N) :
    y ∈ Set.range f ↔ ∀ φ : normalFunctionalSpace N,
      f.predualPullback φ = 0 → (φ : StrongDual ℂ N) y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ φ hφ
    rw [← f.predualPullback_apply φ x, hφ]
    rfl
  · intro hy
    exact f.exists_preimage_of_predual_kernel hf y hy

end

end VonNeumannAlgebra.NormalStarAlgHom
