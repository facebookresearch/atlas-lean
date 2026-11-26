/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Prod

/-! # Observability from linear balances and meter readings -/

@[expose] public section

namespace MathlibExt.LinearAlgebra

/-- **Observability in a linear flowsheet model.** Stack the balance map `A` and the
meter map `H` into `M = A.prod H`. If `x₀` solves `M x = d`, every solution is `x₀ + v`
for a kernel direction `v`, and every such translate is a solution. A linear functional
`ℓ` has the same value `ℓ x₀` on all solutions exactly when it annihilates the kernel.
This concerns the whole affine fiber, not its intersection with the nonnegative orthant.
For kernel background see J. Lebl, *Notes on Diffy Qs*, Appendix A.4.2. -/
theorem flowsheet_observability {E B R : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup R] [Module ℝ R]
    (A : E →ₗ[ℝ] B) (H : E →ₗ[ℝ] R) (ℓ : E →ₗ[ℝ] ℝ) {d : B × R} {x₀ : E}
    (hx₀ : (A.prod H) x₀ = d) :
    let M := A.prod H
    {x | M x = d} = (fun v => x₀ + v) '' (LinearMap.ker M : Set E) ∧
      ((∀ x, M x = d → ℓ x = ℓ x₀) ↔ LinearMap.ker M ≤ LinearMap.ker ℓ) := by
  intro M
  have hx₀M : M x₀ = d := hx₀
  have htranslate (v : E) (hv : v ∈ LinearMap.ker M) : M (x₀ + v) = d := by
    rw [map_add, hx₀M, LinearMap.mem_ker.mp hv, add_zero]
  have hdiff (x : E) (hx : M x = d) : x - x₀ ∈ LinearMap.ker M :=
    LinearMap.sub_mem_ker_iff.mpr (hx.trans hx₀M.symm)
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      refine ⟨x - x₀, hdiff x hx, ?_⟩
      change x₀ + (x - x₀) = x
      rw [add_comm x₀, sub_add_cancel]
    · rintro ⟨v, hv, rfl⟩
      exact htranslate v hv
  · constructor
    · intro h v hv
      have hv' := h (x₀ + v) (htranslate v hv)
      rw [map_add] at hv'
      exact LinearMap.mem_ker.mpr (add_left_cancel (hv'.trans (add_zero (ℓ x₀)).symm))
    · intro h x hx
      exact LinearMap.sub_mem_ker_iff.mp (h (hdiff x hx))

end MathlibExt.LinearAlgebra
