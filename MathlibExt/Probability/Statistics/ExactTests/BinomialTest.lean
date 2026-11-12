/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialTail
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import Mathlib.Probability.Distributions.Binomial

/-!
# The exact binomial test of a composite one-sided null

For `X ~ Bin(n, p)` and the one-sided null `p ≤ p₀`, the exact upper-tail p-value computed
under the boundary null `Bin(n, p₀)` is valid at every `p` in the null. The point-null case
`p = p₀` is `isValidPValue_upperTailPValue`; the composite case follows because the binomial
upper tail is nondecreasing in `p` (`monotoneOn_binomTail`).

Symmetrically, for the one-sided null `p ≥ p₀`, the exact lower-tail p-value computed under
the boundary null `Bin(n, p₀)` is valid at every `p` in the null. The point-null case is
`isValidPValue_lowerTailPValue`; the composite case follows because the binomial lower tail
is nonincreasing in `p` (again `monotoneOn_binomTail`, via `binomial_real_Iic`).

The formal proof uses exactly two ingredients: the p-value is computed at the boundary `p₀`, and
the binomial tail is monotone in the success probability. For a level `s`, the upper-tail
rejection event `{π(X) ≤ s}` is `{X ≥ k₀}` for the least cutoff `k₀` whose tail under
`Bin(n, p₀)` is at most `s`, and for `p ≤ p₀`, `P_p(X ≥ k₀) ≤ P_{p₀}(X ≥ k₀) ≤ s`. The
monotonicity ingredient is `monotoneOn_binomTail`.

## Main results

* `upperTail_binomial`: the upper tail of Mathlib's `binomial` measure is `binomTail`.
* `binomial_real_Iic`: the lower tail of Mathlib's `binomial` measure is `1 - binomTail`.
* `isValidPValue_upperTailPValue_binomial_of_le`
* `isValidPValue_lowerTailPValue_binomial_of_ge`

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  Lemma 3.3.1.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  Wiley, 1968 (binomial tails).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Probability.Statistics.ExactTests

/-- The upper tail `P(X ≥ x)` of Mathlib's `Bin(n, p)` is `binomTail n x p`. -/
theorem upperTail_binomial (n x : ℕ) (p : unitInterval) :
    upperTail (binomial n p) x = binomTail n x p := by
  have hae : ∀ᵐ j ∂(binomial n p), j ≤ n := ae_le_of_hasLaw_binomial HasLaw.id
  have hset : {j : ℕ | x ≤ j} =ᵐ[binomial n p] (↑(Finset.Icc x n) : Set ℕ) := by
    filter_upwards [hae] with j hj
    simp [hj]
  rw [upperTail, measureReal_congr hset, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun j _ => binomial_real_singleton n j p

/-- **Exact binomial test of the composite one-sided null `p ≤ p₀`.** If `X ~ Bin(n, p)` with
`p ≤ p₀`, the exact upper-tail p-value computed under the boundary null `Bin(n, p₀)` is valid:
`μ {upperTail Bin(n, p₀) X ≤ s} ≤ s` for every `s ∈ [0, 1]`.

The proof combines the boundary p-value with `monotoneOn_binomTail`, the monotonicity of the
binomial upper tail in the success probability.

Source: Lehmann–Romano (2005), Lemma 3.3.1; Feller (1968) (binomial tails). -/
theorem isValidPValue_upperTailPValue_binomial_of_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {p p₀ : unitInterval} (hp : (p : ℝ) ≤ p₀) {X : Ω → ℕ}
    (hX : HasLaw X (binomial n p) μ) :
    IsValidPValue μ (upperTailPValue (binomial n p₀) X) := by
  intro s _
  by_cases hS : ∃ k, upperTail (binomial n p₀) k ≤ s
  · classical
    have hset : {ω | upperTailPValue (binomial n p₀) X ω ≤ s} = {ω | Nat.find hS ≤ X ω} := by
      ext ω
      simp only [upperTailPValue, Set.mem_ofPred_eq]
      exact ⟨fun h => Nat.find_min' hS h,
        fun h => (upperTail_antitone _ h).trans (Nat.find_spec hS)⟩
    rw [hset, hX.measure_eq (p := (Nat.find hS ≤ ·)) (measurableSet_Ici (a := Nat.find hS)),
      ← ofReal_measureReal]
    have hmono : upperTail (binomial n p) (Nat.find hS) ≤
        upperTail (binomial n p₀) (Nat.find hS) := by
      rw [upperTail_binomial, upperTail_binomial]
      exact monotoneOn_binomTail n _ p.2 p₀.2 hp
    exact ENNReal.ofReal_le_ofReal (hmono.trans (Nat.find_spec hS))
  · have hset : {ω | upperTailPValue (binomial n p₀) X ω ≤ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => hS ⟨X ω, h⟩
    simp [hset]

/-- The lower tail `P(X ≤ x)` of Mathlib's `Bin(n, p)` is `1 - binomTail n (x + 1) p`. -/
theorem binomial_real_Iic (n x : ℕ) (p : unitInterval) :
    (binomial n p).real (Iic x) = 1 - binomTail n (x + 1) p := by
  have hc : Iic x = {j : ℕ | x + 1 ≤ j}ᶜ := by
    ext j
    simp only [mem_Iic, mem_compl_iff, mem_ofPred_eq, not_le]
    omega
  rw [hc, probReal_compl_eq_one_sub (MeasurableSet.of_discrete), ← upperTail,
    upperTail_binomial]

/-- **Exact binomial test of the composite one-sided null `p ≥ p₀`.** If `X ~ Bin(n, p)`
with `p₀ ≤ p`, the exact lower-tail p-value computed under the boundary null `Bin(n, p₀)`
is valid. -/
theorem isValidPValue_lowerTailPValue_binomial_of_ge {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {p p₀ : unitInterval} (hp : (p₀ : ℝ) ≤ (p : ℝ)) {X : Ω → ℕ}
    (hX : HasLaw X (binomial n p) μ) :
    IsValidPValue μ (lowerTailPValue (binomial n p₀) X) := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
  by_cases hs_lt : s < 1
  · by_cases hS : ∃ k, lowerTail (binomial n p₀) k ≤ s
    · classical
      have htail_ge : ∀ k : ℕ, n ≤ k → lowerTail (binomial n p₀) k = 1 := by
        intro k hk
        unfold lowerTail
        have hI : {j : ℕ | j ≤ k} = Set.Iic k := rfl
        rw [hI, binomial_real_Iic]
        have hempty : Finset.Icc (k + 1) n = ∅ :=
          Finset.Icc_eq_empty_of_lt (by omega)
        unfold binomTail
        rw [hempty, Finset.sum_empty, sub_zero]
      have hbound : ∀ k : ℕ, lowerTail (binomial n p₀) k ≤ s → k ≤ n := by
        intro k hk
        by_contra hcon
        have hlt' : n < k := lt_of_not_ge hcon
        have hle : n ≤ k := le_of_lt hlt'
        have heq : lowerTail (binomial n p₀) k = 1 := htail_ge k hle
        rw [heq] at hk
        exact absurd hk (not_le_of_gt hs_lt)
      obtain ⟨k, hk⟩ := hS
      have hk_le : k ≤ n := hbound k hk
      have hk₀_spec :
          lowerTail (binomial n p₀)
            (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n) ≤ s :=
        Nat.findGreatest_spec (P := fun k => lowerTail (binomial n p₀) k ≤ s) hk_le hk
      have hset : {ω | lowerTailPValue (binomial n p₀) X ω ≤ s} =
          {ω | X ω ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} := by
        ext ω
        simp only [lowerTailPValue, Set.mem_ofPred_eq]
        constructor
        · intro h
          have hleN : X ω ≤ n := hbound _ h
          exact Nat.le_findGreatest (P := fun k => lowerTail (binomial n p₀) k ≤ s) hleN h
        · intro h
          exact le_trans (lowerTail_mono (binomial n p₀) h) hk₀_spec
      have hmeas_eq : μ {ω | X ω ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} =
          (binomial n p) {j | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} :=
        hX.measure_eq
          (measurableSet_Iic
            (a := Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n))
      rw [hset, hmeas_eq, ← ofReal_measureReal]
      have hmono_tail : (binomial n p).real
            {j | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} ≤
          (binomial n p₀).real
            {j | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} := by
        have hI : {j : ℕ | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} =
            Set.Iic (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n) := rfl
        rw [hI]
        have hp₀mem : (p₀ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨unitInterval.nonneg _, unitInterval.le_one _⟩
        have hpmem : (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨unitInterval.nonneg _, unitInterval.le_one _⟩
        have hbt : binomTail n
              (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n + 1) (p₀ : ℝ) ≤
            binomTail n
              (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n + 1) (p : ℝ) :=
          monotoneOn_binomTail n
            (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n + 1) hp₀mem hpmem hp
        have h1 := binomial_real_Iic n
          (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n) p
        have h2 := binomial_real_Iic n
          (Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n) p₀
        rw [h1, h2]
        exact sub_le_sub_left hbt 1
      have hk₀_real : (binomial n p₀).real
          {j | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} ≤ s :=
        hk₀_spec
      have hle_real : (binomial n p).real
          {j | j ≤ Nat.findGreatest (fun k => lowerTail (binomial n p₀) k ≤ s) n} ≤ s :=
        le_trans hmono_tail hk₀_real
      exact ENNReal.ofReal_le_ofReal hle_real
    · have hset : {ω | lowerTailPValue (binomial n p₀) X ω ≤ s} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω h => hS ⟨X ω, h⟩
      simp [hset]
  · have hs_eq : s = 1 := le_antisymm hs1 (le_of_not_gt hs_lt)
    subst hs_eq
    have hmeas : MeasurableSet {x : ℕ | lowerTail (binomial n p₀) x ≤ 1} :=
      MeasurableSet.of_discrete
    have heq : μ {ω | lowerTailPValue (binomial n p₀) X ω ≤ 1} =
        (binomial n p) {x | lowerTail (binomial n p₀) x ≤ 1} :=
      hX.measure_eq hmeas
    rw [heq]
    calc (binomial n p) {x | lowerTail (binomial n p₀) x ≤ 1} ≤ (binomial n p) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm

end MathlibExt.Probability.Statistics.ExactTests
