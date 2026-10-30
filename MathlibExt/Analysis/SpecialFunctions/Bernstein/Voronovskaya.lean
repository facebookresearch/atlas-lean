/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.Factorial.Cast

/-!
# Voronovskaya's theorem for Bernstein polynomials

For `f : C([0, 1], ℝ)` the `n`-th Bernstein approximation is
`bernsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f (k / n)`, the expected
value of `f (S / n)` for `S ~ Bin(n, x)`. Mathlib proves that it converges uniformly to `f`
(`bernsteinApproximation_uniform`). Voronovskaya's theorem identifies the rate: for `f` of
class `C²`,

  `n · (bernsteinApproximation n f x - f x) → x (1 - x) / 2 · f''(x)`.

The proof uses the central moments `∑ k, (x - k / n) ^ j * bernstein n k x` of the Bernstein
weights: `j = 0` is `bernstein.probability`, `j = 2` is `bernstein.variance` (both in Mathlib);
this file adds the first moment (`j = 1`, which vanishes) and the exact fourth moment
`x (1 - x) (1 + 3 (n - 2) x (1 - x)) / n ^ 3`, which is `O(1 / n ^ 2)` uniformly in `x`.

In population genetics the same statement is the generator half of the diffusion approximation
of the neutral Wright–Fisher model; see
`MathlibExt.Biology.PopulationGenetics.Diffusion.DiffusionLimit`.

## Main results

* `bernstein.mean`: `∑ k, (x - k / n) * bernstein n k x = 0` for `n ≠ 0`.
* `bernstein.fourth_moment`: the exact fourth central moment.
* `bernstein.fourth_moment_le`: the fourth central moment is at most `1 / n ^ 2`.
* `bernsteinApproximation.tendsto_voronovskaya`: Voronovskaya's theorem for `C²` functions.

## References

* E. V. Voronovskaya, *Détermination de la forme asymptotique d'approximation des fonctions par
  les polynômes de M. Bernstein*, C. R. Acad. Sci. URSS (1932) 79–85.
* G. G. Lorentz, *Bernstein Polynomials*, University of Toronto Press (1953), Chapter 1.
-/

@[expose] public section

open Filter
open scoped unitInterval Topology

namespace bernstein

/-- Factorial moments of the Bernstein weights:
`∑ k, k (k - 1) ⋯ (k - j + 1) b_{n,k}(x) = n (n - 1) ⋯ (n - j + 1) x ^ j`. -/
private theorem factorial_moment (n j : ℕ) (x : I) :
    (∑ k ∈ Finset.range (n + 1), (k.descFactorial j : ℝ) * bernstein n k x) =
      (n.descFactorial j : ℝ) * (x : ℝ) ^ j := by
  classical
  by_cases hj : j ≤ n
  · have hc (k : ℕ) :
        (j + k).descFactorial j * n.choose (j + k) =
          n.descFactorial j * (n - j).choose k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose]
      have h := Nat.choose_mul (n := n) (Nat.le_add_right j k)
      simp only [Nat.add_sub_cancel_left] at h
      nlinarith
    rw [show n + 1 = j + (n - j + 1) by omega, Finset.sum_range_add]
    have hz : (∑ k ∈ Finset.range j,
        (k.descFactorial j : ℝ) * bernstein n k x) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [Nat.descFactorial_of_lt (Finset.mem_range.mp hk)]
    rw [hz, zero_add]
    calc
      _ = (n.descFactorial j : ℝ) * (x : ℝ) ^ j *
          ∑ k ∈ Finset.range (n - j + 1), bernstein (n - j) k x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [bernstein_apply]
        rw [show n - (j + k) = n - j - k by omega, pow_add]
        have hc' : ((j + k).descFactorial j : ℝ) * (n.choose (j + k) : ℝ) =
            (n.descFactorial j : ℝ) * ((n - j).choose k : ℝ) := by
          exact_mod_cast hc k
        calc
          _ = (((j + k).descFactorial j : ℝ) * (n.choose (j + k) : ℝ)) *
              ((x : ℝ) ^ j * (x : ℝ) ^ k * (1 - x) ^ (n - j - k)) := by ring
          _ = _ := by rw [hc']; ring
      _ = _ := by
        have hp : (∑ k ∈ Finset.range (n - j + 1), bernstein (n - j) k x) = 1 := by
          simpa only [Finset.sum_range] using probability (n - j) x
        rw [hp, mul_one]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge hj)]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    simp [Nat.descFactorial_of_lt (show k < j by
      have := Finset.mem_range.mp hk
      omega)]

/-- `n (n - 1) (n - 2)` as a real number. -/
private theorem cast_factorial_three (n : ℕ) :
    (n.descFactorial 3 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) := by
  rcases n with _ | _ | n
  · norm_num [Nat.descFactorial]
  · norm_num [Nat.descFactorial]
  · simp [Nat.descFactorial, Nat.cast_add, Nat.cast_mul]
    ring

/-- `n (n - 1) (n - 2) (n - 3)` as a real number. -/
private theorem cast_factorial_four (n : ℕ) :
    (n.descFactorial 4 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) * (n - 3) := by
  rcases n with _ | _ | _ | n
  · norm_num [Nat.descFactorial]
  · norm_num [Nat.descFactorial]
  · norm_num [Nat.descFactorial]
  · simp [Nat.descFactorial, Nat.cast_add, Nat.cast_mul]
    ring

/-- **First central moment of the Bernstein weights.** For `n ≠ 0`,
`∑ k : Fin (n + 1), (x - k / n) * bernstein n k x = 0`: the binomial frequency `S / n` has
mean `x`. -/
theorem mean {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), ((x : ℝ) - z k) * bernstein n k x) = 0 := by
  have hsum : (∑ k : Fin (n + 1), (k : ℝ) * bernstein n k x) = n * (x : ℝ) := by
    simpa [Finset.sum_range] using factorial_moment n 1 x
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [z, sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, probability, hsum, mul_one]
  field_simp
  ring

/-- **Fourth central moment of the Bernstein weights.** For `n ≠ 0`,
`∑ k : Fin (n + 1), (x - k / n) ^ 4 * bernstein n k x = x (1 - x) (1 + 3 (n - 2) x (1 - x)) / n³`,
i.e. `E[(S - n x) ^ 4] = n x (1 - x) (1 + 3 (n - 2) x (1 - x))` for `S ~ Bin(n, x)`. -/
theorem fourth_moment {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), ((x : ℝ) - z k) ^ 4 * bernstein n k x) =
      (x : ℝ) * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) / (n : ℝ) ^ 3 := by
  have hp : (∑ k ∈ Finset.range (n + 1), bernstein n k x) = 1 := by
    simpa only [Finset.sum_range] using probability n x
  have h : (∑ k ∈ Finset.range (n + 1),
      ((n : ℝ) * x - k) ^ 4 * bernstein n k x) =
      n * (x : ℝ) * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) := by
    calc
      _ = (∑ k ∈ Finset.range (n + 1), (k.descFactorial 4 : ℝ) * bernstein n k x) +
          (6 - 4 * n * (x : ℝ)) *
            (∑ k ∈ Finset.range (n + 1), (k.descFactorial 3 : ℝ) * bernstein n k x) +
          (7 - 12 * n * (x : ℝ) + 6 * ((n : ℝ) * x) ^ 2) *
            (∑ k ∈ Finset.range (n + 1), (k.descFactorial 2 : ℝ) * bernstein n k x) +
          (1 - 4 * n * (x : ℝ) + 6 * ((n : ℝ) * x) ^ 2 - 4 * ((n : ℝ) * x) ^ 3) *
            (∑ k ∈ Finset.range (n + 1), (k.descFactorial 1 : ℝ) * bernstein n k x) +
          ((n : ℝ) * x) ^ 4 * (∑ k ∈ Finset.range (n + 1), bernstein n k x) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [cast_factorial_four, cast_factorial_three, Nat.cast_descFactorial_two]
        simp only [Nat.descFactorial_one]
        ring
      _ = _ := by
        rw [factorial_moment, factorial_moment, factorial_moment, factorial_moment, hp,
          cast_factorial_four, cast_factorial_three, Nat.cast_descFactorial_two]
        simp only [Nat.descFactorial_one]
        ring
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  convert congrArg (fun y : ℝ => y / (n : ℝ) ^ 4) h using 1
  · simp only [Finset.sum_range, z]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    field_simp
  · field_simp

/-- The fourth central moment of the Bernstein weights is at most `1 / n ^ 2`, uniformly in
`x ∈ [0, 1]`. -/
theorem fourth_moment_le {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), ((x : ℝ) - z k) ^ 4 * bernstein n k x) ≤ 1 / (n : ℝ) ^ 2 := by
  rw [fourth_moment hn]
  have hn₁ : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hn₀ : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn₁
  have hx₀ := x.property.1
  have hx₁ := x.property.2
  have hp₀ : 0 ≤ (x : ℝ) * (1 - x) := mul_nonneg hx₀ (sub_nonneg.mpr hx₁)
  have hp₁ : (x : ℝ) * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]
  have hp₂ : ((x : ℝ) * (1 - x)) ^ 2 ≤ 1 / 16 := by nlinarith
  apply (div_le_iff₀ (pow_pos hn₀ 3)).mpr
  have he : 1 / (n : ℝ) ^ 2 * (n : ℝ) ^ 3 = n := by field_simp
  rw [he]
  nlinarith [mul_nonneg hn₀.le (sub_nonneg.mpr hp₂),
    sq_nonneg ((x : ℝ) * (1 - x))]

end bernstein

namespace bernsteinApproximation

/-- Peano form of Taylor's theorem on `[0, 1]`: `f t` is its second-order Taylor polynomial
at `x` plus `g t (t - x)²` with `g` continuous on `[0, 1]` and `g x = 0`. -/
private theorem quadratic_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : I) :
    ∃ g : C(I, ℝ), g x = 0 ∧ ∀ t : I,
      f t = f x + deriv f x * ((t : ℝ) - x) +
        deriv (deriv f) x / 2 * ((t : ℝ) - x) ^ 2 + g t * ((t : ℝ) - x) ^ 2 := by
  let P : ℝ → ℝ := fun t => f x + deriv f x * (t - x) +
    deriv (deriv f) x / 2 * (t - x) ^ 2
  have hP (t : ℝ) : taylorWithinEval f 2 Set.univ x t = P t := by
    norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ, P]
    ring
  let g : ℝ → ℝ := fun t => (f t - P t) / (t - x) ^ 2
  have hgx : g x = 0 := by simp [g, P]
  have hlim : Tendsto g (𝓝 (x : ℝ)) (𝓝 0) := by
    have h := Real.taylor_tendsto (n := 2) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ (x : ℝ)) hf.contDiffOn
    simpa only [nhdsWithin_univ, hP] using h
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t = (x : ℝ)
    · subst t
      change Tendsto g (𝓝 (x : ℝ)) (𝓝 (g x))
      rw [hgx]
      exact hlim
    · have hPc : Continuous P := by unfold P; fun_prop
      exact (hf.continuous.continuousAt.sub hPc.continuousAt).div
        ((continuousAt_id.sub continuousAt_const).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr ht))
  refine ⟨⟨fun t => g t, hg.comp continuous_subtype_val⟩, hgx, ?_⟩
  intro t
  change f t = P t + g t * ((t : ℝ) - x) ^ 2
  by_cases ht : (t : ℝ) = x
  · simp [g, P, ht]
  · dsimp [g]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr ht))]
    ring

/-- **Voronovskaya's theorem (1932).** For `f : ℝ → ℝ` of class `C²` and `x ∈ [0, 1]`, the
Bernstein approximations of `f` on `[0, 1]` satisfy
`n · (bernsteinApproximation n f x - f x) → x (1 - x) / 2 · f''(x)` as `n → ∞`.

Source: Voronovskaya (1932); Lorentz, *Bernstein Polynomials* (1953), Chapter 1. -/
theorem tendsto_voronovskaya {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : I) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        (bernsteinApproximation n ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).restrict I) x - f x))
      atTop (𝓝 ((x : ℝ) * (1 - x) / 2 * deriv (deriv f) x)) := by
  classical
  obtain ⟨g, hgx, hg⟩ := quadratic_remainder hf x
  let q : C(I, ℝ) := ⟨fun t => g t ^ 2, g.continuous.pow 2⟩
  let r : ℕ → ℝ := fun n => ∑ k : Fin (n + 1),
    g (bernstein.z k) * ((x : ℝ) - bernstein.z k) ^ 2 * bernstein n k x
  have hdecomp (n : ℕ) (hn : n ≠ 0) :
      (n : ℝ) *
          (bernsteinApproximation n ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).restrict I) x - f x) =
        (x : ℝ) * (1 - x) / 2 * deriv (deriv f) x + (n : ℝ) * r n := by
    have he : bernsteinApproximation n ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).restrict I) x =
        f x * (∑ k : Fin (n + 1), bernstein n k x) -
        deriv f x * (∑ k : Fin (n + 1),
          ((x : ℝ) - bernstein.z k) * bernstein n k x) +
        deriv (deriv f) x / 2 * (∑ k : Fin (n + 1),
          ((x : ℝ) - bernstein.z k) ^ 2 * bernstein n k x) + r n := by
      simp only [apply, ContinuousMap.restrict_apply, ContinuousMap.coe_mk, smul_eq_mul, r,
        Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hg (bernstein.z k)]
      ring
    rw [he, bernstein.probability, bernstein.mean hn, bernstein.variance hn]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    ring
  have hcs (n : ℕ) : (r n) ^ 2 ≤
      (∑ k : Fin (n + 1), ((x : ℝ) - bernstein.z k) ^ 4 * bernstein n k x) *
        bernsteinApproximation n q x := by
    rw [apply]
    simp only [smul_eq_mul]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro k hk
      positivity
    · intro k hk
      exact mul_nonneg (bernstein_nonneg) (sq_nonneg _)
    · intro k hk
      change (g (bernstein.z k) * ((x : ℝ) - bernstein.z k) ^ 2 * bernstein n k x) ^ 2 ≤
        (((x : ℝ) - bernstein.z k) ^ 4 * bernstein n k x) *
          (bernstein n k x * g (bernstein.z k) ^ 2)
      apply le_of_eq
      ring
  have hbound (n : ℕ) (hn : n ≠ 0) : ((n : ℝ) * r n) ^ 2 ≤
      bernsteinApproximation n q x := by
    have hq : 0 ≤ bernsteinApproximation n q x := by
      rw [apply]
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg bernstein_nonneg (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left (hcs n) (sq_nonneg (n : ℝ))
    have hm := mul_le_mul_of_nonneg_right (bernstein.fourth_moment_le hn x) hq
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have he : (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2 * bernsteinApproximation n q x) =
        bernsteinApproximation n q x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg (n : ℝ))]
  have hq : Tendsto (fun n : ℕ => bernsteinApproximation n q x) atTop (𝓝 0) := by
    have h := (continuous_eval_const x).tendsto q
    simpa [q, hgx, Function.comp_def] using h.comp (bernsteinApproximation_uniform q)
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * r n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hq.eventually_lt_const (sq_pos_of_pos hε), eventually_ne_atTop 0]
      with n hnq hn
    rw [Real.dist_eq, sub_zero]
    apply (sq_lt_sq₀ (abs_nonneg _) hε.le).mp
    simpa only [sq_abs] using lt_of_le_of_lt (hbound n hn) hnq
  apply Tendsto.congr' (show ∀ᶠ n : ℕ in atTop,
      (x : ℝ) * (1 - x) / 2 * deriv (deriv f) x + (n : ℝ) * r n =
        (n : ℝ) *
          (bernsteinApproximation n ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).restrict I) x - f x) from ?_)
      (by simpa using tendsto_const_nhds.add hr)
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (hdecomp n hn).symm

end bernsteinApproximation
