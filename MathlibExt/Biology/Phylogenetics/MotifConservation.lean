/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DeMoivreLaplace
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Nat.Choose.Sum

/-!
# The motif conservation score: binomial tails and their normal limit

Xie et al. (2005) measure the excess conservation of a motif with `N` occurrences, `k` of them
conserved across the aligned genomes, against the conservation probability `p` of comparable
random motifs. Under the null model the number of conserved occurrences is `Bin(N, p)`; the
evidence is the binomial upper tail `P(Bin(N, p) ≥ k)`, and the **motif conservation score**
(MCS) is described as essentially the number of standard deviations by which the observed
conservation exceeds the expected one. We formalize the binomial tail and the binomial
z-score `(k - N p) / √(N p (1 - p))` (`mcsApprox`): this is a binomial z-score
approximation to the MCS, not Xie et al.'s exact score, which may differ in detail
(see their Methods).

## Main results

* `binomTail_succ_le`: the tail is nonincreasing in `k` (for `p ∈ [0, 1]`);
  `binomTail_zero`, `binomTail_of_lt`: the boundary values `1` and `0`.
* `hasDerivAt_binomTail`: `d/dp P(Bin(n, p) ≥ k) = n C(n - 1, k - 1) p^(k-1) (1 - p)^(n-k)`.
* `monotoneOn_binomTail`, `strictMonoOn_binomTail`: the tail is (strictly, for `1 ≤ k ≤ n`)
  increasing in `p` on `[0, 1]`: a higher background conservation rate makes the same count
  less surprising.
* `mcsApprox_strictMono`: the MCS approximation is strictly increasing in the conserved count.
* `tendsto_prob_le_mcsApprox`: **de Moivre–Laplace for the MCS approximation**: for i.i.d.
  Bernoulli(`p`) conservation indicators, `P(z ≤ MCS approximation)` tends to the standard
  normal mass of `[z, ∞)`.

## References

* X. Xie, J. Lu, E. J. Kulbokas, T. R. Golub, V. Mootha, K. Lindblad-Toh, E. S. Lander,
  M. Kellis, *Systematic discovery of regulatory motifs in human promoters and 3′ UTRs by
  comparison of several mammals*, Nature 434 (2005), 338–345.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  Wiley, 1968 (binomial tails and the normal approximation).
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace MathlibExt.Biology.Phylogenetics.MotifConservation

/-- The upper tail `P(X ≥ k) = ∑_{i = k}^{n} C(n, i) p^i (1 - p)^(n - i)` of the binomial law
`Bin(n, p)`. -/
noncomputable def binomTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Icc k n, (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- `P(X ≥ 0) = 1`, for every real `p` (the binomial theorem). -/
theorem binomTail_zero (n : ℕ) (p : ℝ) : binomTail n 0 p = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  have hI : Icc 0 n = range (n + 1) := by ext i; simp
  rw [binomTail, hI]
  exact (sum_congr rfl fun i _ => by ring).trans h

/-- `P(X ≥ k) = 0` for `k > n`. -/
theorem binomTail_of_lt {n k : ℕ} (h : n < k) (p : ℝ) : binomTail n k p = 0 := by
  rw [binomTail, Icc_eq_empty (not_le.2 h), sum_empty]

/-- **The tail is nonincreasing in `k`** for `p ∈ [0, 1]`. -/
theorem binomTail_succ_le (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomTail n (k + 1) p ≤ binomTail n k p :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (Nat.le_succ k)) fun _ _ _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg (sub_nonneg.2 hp1) _)

private theorem sum_Icc_pred_sub {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (f : ℕ → ℝ) :
    (∑ i ∈ Icc k n, (f (i - 1) - f i)) = f (k - 1) - f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k ≤ n
    · rw [sum_Icc_succ_top (by omega), ih h]
      simp only [Nat.add_sub_cancel]
      ring
    · have he : k = n + 1 := by omega
      subst k
      simp

private theorem hasDerivAt_binomTerm {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (p : ℝ) :
    HasDerivAt (fun p : ℝ => (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i))
      ((n : ℝ) * (((n - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (n - i) -
        ((n - 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n - 1 - i))) p := by
  have hn : n - 1 + 1 = n := by omega
  have hi' : i - 1 + 1 = i := by omega
  have hc₁ : (n.choose i : ℝ) * (i : ℝ) =
      (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (i - 1)
    rw [hn, hi'] at h
    exact_mod_cast h.symm
  have hc₂ : (n.choose i : ℝ) * (n - i : ℕ) =
      (n : ℝ) * ((n - 1).choose i : ℝ) := by
    have h := Nat.choose_mul_succ_eq (n - 1) i
    rw [hn] at h
    exact_mod_cast h.symm.trans (Nat.mul_comm _ _)
  have he : n - i - 1 = n - 1 - i := by omega
  convert ((hasDerivAt_pow i p).const_mul (n.choose i : ℝ)).mul
    (((hasDerivAt_id p).const_sub 1).pow (n - i)) using 1
  · rfl
  · simp only [he, Pi.pow_apply, id_eq]
    symm
    calc
      _ = ((n.choose i : ℝ) * (i : ℝ)) * p ^ (i - 1) * (1 - p) ^ (n - i) -
          ((n.choose i : ℝ) * (n - i : ℕ)) * p ^ i * (1 - p) ^ (n - 1 - i) := by
        ring
      _ = _ := by rw [hc₁, hc₂]; ring

/-- **Derivative of the binomial upper tail** in the success probability: for `1 ≤ k ≤ n`,
`d/dp P(Bin(n, p) ≥ k) = n C(n - 1, k - 1) p^(k-1) (1-p)^(n-k)` at every real `p` (the sum
telescopes). -/
theorem hasDerivAt_binomTail {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (p : ℝ) :
    HasDerivAt (binomTail n k)
      (n * ((n - 1).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (n - k)) p := by
  let A : ℕ → ℝ := fun i =>
    ((n - 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n - 1 - i)
  have hd : HasDerivAt (binomTail n k)
      (∑ i ∈ Icc k n, (n : ℝ) * (A (i - 1) - A i)) p := by
    unfold binomTail
    apply HasDerivAt.fun_sum
    intro i hi
    have hki := (mem_Icc.mp hi).1
    have hin := (mem_Icc.mp hi).2
    have hi' : 1 ≤ i := hk.trans hki
    have he : n - 1 - (i - 1) = n - i := by omega
    simpa only [A, he] using hasDerivAt_binomTerm hi' hin p
  have hn : n - 1 < n := by omega
  have he : n - 1 - (k - 1) = n - k := by omega
  have hsum : (∑ i ∈ Icc k n, (n : ℝ) * (A (i - 1) - A i)) =
      n * ((n - 1).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (n - k) := by
    rw [← mul_sum, sum_Icc_pred_sub hk hkn]
    simp only [A, Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul, sub_zero, he]
    ring
  exact hsum ▸ hd

/-- **The binomial upper tail is nondecreasing in `p` on `[0, 1]`**, for every `n` and `k`. -/
theorem monotoneOn_binomTail (n k : ℕ) : MonotoneOn (binomTail n k) (Set.Icc 0 1) := by
  by_cases hk : k = 0
  · subst k
    intro x hx y hy hxy
    simp only [binomTail_zero]
    exact le_rfl
  by_cases hkn : k ≤ n
  · have hk' : 1 ≤ k := by omega
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro p hp
      exact (hasDerivAt_binomTail hk' hkn p).continuousAt.continuousWithinAt
    · intro p hp
      exact (hasDerivAt_binomTail hk' hkn p).differentiableAt.differentiableWithinAt
    · intro p hp
      rw [interior_Icc] at hp
      rw [(hasDerivAt_binomTail hk' hkn p).deriv]
      have hp₀ : 0 ≤ p := le_of_lt hp.1
      have hp₁ : 0 ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp.2)
      positivity
  · have he : Icc k n = ∅ := Icc_eq_empty_of_lt (by omega)
    intro x hx y hy hxy
    simp only [binomTail, he, sum_empty]
    exact le_rfl

/-- **The binomial upper tail is strictly increasing in `p` on `[0, 1]`** when `1 ≤ k ≤ n`. -/
theorem strictMonoOn_binomTail {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    StrictMonoOn (binomTail n k) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro p hp
    exact (hasDerivAt_binomTail hk hkn p).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_binomTail hk hkn p).deriv]
    have hn : 0 < n := by omega
    have hc : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have hp₀ : 0 < p := hp.1
    have hp₁ : 0 < 1 - p := sub_pos.mpr hp.2
    positivity

/-- **Binomial z-score approximation to the motif conservation score**: the conserved count
`k` of a motif with `N` occurrences, standardized under `Bin(N, p)`:
`(k - N p) / √(N p (1 - p))`. This is an approximation to Xie et al.'s MCS, not their
exact score. -/
noncomputable def mcsApprox (N : ℕ) (k p : ℝ) : ℝ := (k - N * p) / Real.sqrt (N * p * (1 - p))

/-- The MCS approximation is strictly increasing in the conserved count, for `N ≥ 1` and `p ∈ (0, 1)`. -/
theorem mcsApprox_strictMono {N : ℕ} (hN : 0 < N) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMono fun k => mcsApprox N k p := by
  intro a b hab
  have hs : 0 < Real.sqrt (N * p * (1 - p)) :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (Nat.cast_pos.2 hN) hp0) (sub_pos.2 hp1))
  exact div_lt_div_of_pos_right (by linarith) hs

/-- The MCS approximation of the number of conserved occurrences among the first `n` is the
de Moivre–Laplace standardized sum. -/
theorem mcsApprox_sum_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (ω : Ω) :
    mcsApprox n (∑ i ∈ range n, X i ω) p = deMoivreLaplaceStandardized X p n ω := rfl

/-- **De Moivre–Laplace for the MCS approximation**: if the conservation indicators of
the occurrences are i.i.d. Bernoulli(`p`) with `0 < p < 1`, then for every `z`,
`P(z ≤ MCS approximation of the first n occurrences)` tends to the standard normal mass of
`[z, ∞)`. -/
theorem tendsto_prob_le_mcsApprox {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hmean : ∀ i, ∫ ω, X i ω ∂P = p)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (z : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | z ≤ mcsApprox n (∑ i ∈ range n, X i ω) p}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Ici z))) := by
  have hdist := deMoivreLaplace_tendstoInDistribution X hp0 hp1 h01 hmean hindep hident
  have hlim := by simpa [Measure.map_id] using hdist.tendsto
  have hnull : ((⟨gaussianReal 0 (1 : ℝ≥0), inferInstance⟩ : ProbabilityMeasure ℝ)
      : Measure ℝ) (frontier (Set.Ici z)) = 0 := by
    have hns : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    change (gaussianReal 0 (1 : ℝ≥0)) (frontier (Set.Ici z)) = 0
    rw [frontier_Ici]
    exact measure_singleton z
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hnull
  have hport' : Tendsto
      (fun n => (P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Ici z))
      atTop (𝓝 ((gaussianReal 0 1) (Set.Ici z))) :=
    hport
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport'
  have hterm : ∀ n : ℕ, P.real {ω | z ≤ mcsApprox n (∑ i ∈ range n, X i ω) p}
      = ((P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Ici z)).toReal := by
    intro n
    have hmeas : AEMeasurable (fun ω => deMoivreLaplaceStandardized X p n ω) P :=
      hdist.forall_aemeasurable n
    rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ici]
    rfl
  simp_rw [hterm]
  exact hreal

end MathlibExt.Biology.Phylogenetics.MotifConservation
