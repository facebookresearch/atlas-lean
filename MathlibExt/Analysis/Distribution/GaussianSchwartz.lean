/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Gaussian is a Schwartz function

`gaussian_mem_schwartz` realizes the Gaussian on a finite-dimensional real inner product space
as a Schwartz map.
-/

@[expose] public section

open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.GaussianSchwartzWanted

private lemma polynomial_gaussian_bound (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-r ^ 2) ≤ m.factorial * Real.exp 2 := by
  have h := (div_le_iff₀ (by positivity : 0 < (m.factorial : ℝ))).mp
    (Real.pow_div_factorial_le_exp (1 + r) (by linarith) m)
  calc
    _ ≤ (Real.exp (1 + r) * m.factorial) * Real.exp (-r ^ 2) := by gcongr
    _ = m.factorial * Real.exp (1 + r - r ^ 2) := by
      rw [sub_eq_add_neg, Real.exp_add (1 + r)]
      ring
    _ ≤ _ := by gcongr; nlinarith [sq_nonneg (r - 1 / 2)]

/--
**The Gaussian is a Schwartz function.** Let $E$ be a finite-dimensional real inner product
space. Then there is a real-valued Schwartz function $g$ on $E$ such that
$g(x) = e^{-\|x\|^2}$ for every $x \in E$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Spaces S(R^d)" / entry "Gaussian functions";
<https://en.wikipedia.org/wiki/Schwartz_space>.
-/
public theorem gaussian_mem_schwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℝ), ∀ x, g x = Real.exp (-‖x‖ ^ 2) := by
  let q : E → ℝ := fun x ↦ -‖x‖ ^ 2
  have hq : q.HasTemperateGrowth := (Function.hasTemperateGrowth_norm_sq E).neg
  refine ⟨⟨Real.exp ∘ q, Real.contDiff_exp.comp hq.1, ?_⟩, fun _ ↦ rfl⟩
  intro k n
  obtain ⟨d, C, hC, hq_bound⟩ := hq.norm_iteratedFDeriv_le_uniform n
  use n.factorial * (1 + C) ^ n * ((k + d * n).factorial * Real.exp 2)
  intro x
  -- The chain rule retains the Gaussian factor since every derivative of exp equals exp.
  have hderiv : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤
      n.factorial * Real.exp (q x) * ((1 + C) * (1 + ‖x‖) ^ d) ^ n := by
    apply norm_iteratedFDeriv_comp_le Real.contDiff_exp hq.1 (mod_cast le_top) x
    · intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
    · intro i hi hin
      calc
        _ ≤ C * (1 + ‖x‖) ^ d := hq_bound i hin x
        _ ≤ (1 + C) * (1 + ‖x‖) ^ d := by gcongr; linarith
        _ ≤ _ := le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith)
          (one_le_pow₀ (by simp))) (by omega)
  calc
    _ ≤ (1 + ‖x‖) ^ k * (n.factorial * Real.exp (q x) *
        ((1 + C) * (1 + ‖x‖) ^ d) ^ n) := by gcongr; linarith
    _ = n.factorial * (1 + C) ^ n * ((1 + ‖x‖) ^ (k + d * n) * Real.exp (q x)) := by
      rw [mul_pow, pow_add, pow_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_gaussian_bound _ (norm_nonneg x))
      (by positivity)

end MathlibExt.Analysis.Distribution.GaussianSchwartzWanted
