/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass
public import MathlibExt.Probability.HoeffdingBounded

/-!
# Selecting the best of finitely many simulated alternatives

A finite nonempty set `X` of alternatives has unknown costs `C(x)`. Each cost is estimated by
the average `Ĉ(x) = (1/n) ∑ᵢ Yₓᵢ` of `n` replications `Yₓ₁, …, Yₓₙ`: almost-everywhere measurable
real functions on a probability space that are independent, take values in `[a, b]` almost surely
and have mean `C(x)`. The replications of different alternatives may be dependent, as when they
share common random numbers. The alternative selected is one with the smallest estimate.
Probabilities of deviation events are `μ.real`: such an event is null-measurable, and `μ.real` of
it is its probability in the completion of `μ`.

## Main result

- `measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt`: for every `ε ≥ 0`,
  `P(maxₓ |Ĉ(x) - C(x)| ≥ ε) ≤ 2 |X| exp (-2 n ε² / (b - a)²)`, and when
  `maxₓ |Ĉ(x) - C(x)| < ε`, every minimizer `x̂` of `Ĉ` satisfies `C(x̂) - minₓ C(x) < 2 ε`.

## References

- S. Asmussen and P. W. Glynn, *Stochastic Simulation: Algorithms and Analysis*, Springer, 2007:
  background on estimating costs by simulation, not a source for this statement.
- F. Bach, *Learning Theory from First Principles*, MIT Press (2024), author edition of
  26 May 2025: Section 1.2.1, Corollary 1.1 and the first remark after it (two-sided Hoeffding
  inequality on `[a, b]`); Section 4.4.3 (union bound over a finite class); Section 4.4,
  equation (4.10) and the sentence after it (twice the largest deviation). These are the
  ingredients of the proof, not a source for the whole statement.

## Proof outline

For a fixed alternative, the two-sided Hoeffding inequality for averages of independent bounded
variables (`MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le`) bounds the
probability that `|Ĉ(x) - C(x)| ≥ ε` by `2 exp (-2 n ε² / (b - a)²)`; it uses the independence of
the replications of that alternative only. The event `maxₓ |Ĉ(x) - C(x)| ≥ ε` is the union of
these `|X|` events, so a union bound gives the first claim, whatever the dependence between
alternatives. For the second, if every deviation is at most `s < ε` and `x̂` minimizes `Ĉ`, then
`C(x̂) ≤ Ĉ(x̂) + s ≤ Ĉ(x) + s ≤ C(x) + 2 s` for every `x`, the decomposition behind empirical
risk minimization
(`CSLibExt.MachineLearning.GeneralizationBounds.risk_le_add_two_mul_of_forall_abs_sub_le`),
applied to a minimizer of `C`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace Cslib.Algorithms.Simulation.SelectBest

/-- **Uniform error and regret for selecting the best simulated alternative.** Let `X` be a
finite nonempty set of alternatives and, for each `x ∈ X`, let `Yₓ₁, …, Yₓₙ` be independent
almost-everywhere measurable real functions on a probability space, with values in `[a, b]`
almost surely and mean `C(x)`; the replications of different alternatives may be dependent.
Write `Ĉ(x) = (1/n) ∑ᵢ Yₓᵢ`. Then for every `ε ≥ 0`,
`P(maxₓ |Ĉ(x) - C(x)| ≥ ε) ≤ 2 |X| exp (-2 n ε² / (b - a)²)`, and at every outcome where
`maxₓ |Ĉ(x) - C(x)| < ε`, every minimizer `x̂` of `Ĉ` satisfies `C(x̂) - minₓ C(x) < 2 ε`.

The bound needs neither `n ≥ 1` nor `a < b`: an average of no replications is `0` and a quotient
by `0` is `0` (Lean's convention), so the right-hand side is `2 |X| ≥ 1` when `n = 0` or `a = b`;
when `a > b`, no replication takes values in `[a, b]` almost surely. For `ε = 0` the second
claim is vacuous. The replications need not be measurable, so neither need the deviation event;
it is null-measurable, and `P` of it is `μ.real`, its probability in the completion of `μ`. The
claim about minimizers holds outcome by outcome.

Background: S. Asmussen and P. W. Glynn, *Stochastic Simulation: Algorithms and Analysis*,
Springer, 2007 (estimating costs by simulation; not a source for this statement). Ingredients:
F. Bach, *Learning Theory from First Principles*, MIT Press (2024), author edition of
26 May 2025, Corollary 1.1 and the first remark after it, Section 4.4.3 and equation (4.10);
they are not a source for the whole statement.
Proof: the two-sided Hoeffding inequality for each alternative and a union bound over `X`; then
`C(x̂) ≤ Ĉ(x̂) + s ≤ Ĉ(x) + s ≤ C(x) + 2 s` for the largest deviation `s < ε`. -/
theorem measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt {Ω X : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype X] [Nonempty X] {n : ℕ}
    {Y : X → Fin n → Ω → ℝ} (h_indep : ∀ x, iIndepFun (Y x) μ)
    (hmeas : ∀ x i, AEMeasurable (Y x i) μ) {a b : ℝ}
    (hY : ∀ x i, ∀ᵐ ω ∂μ, Y x i ω ∈ Set.Icc a b) {C : X → ℝ} (hC : ∀ x i, μ[Y x i] = C x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} ≤
      2 * Fintype.card X * exp (-2 * n * ε ^ 2 / (b - a) ^ 2) ∧
    ∀ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|) < ε →
      ∀ xhat, (∀ x, (1 / n : ℝ) * ∑ i, Y xhat i ω ≤ (1 / n : ℝ) * ∑ i, Y x i ω) →
        C xhat - Finset.univ.inf' Finset.univ_nonempty C < 2 * ε := by
  refine ⟨?_, fun ω hω xhat hmin => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hcard : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul, zero_div, exp_zero, mul_one]
      exact measureReal_le_one.trans (by linarith)
    have hone : ∀ x, μ.real {ω | ε ≤ |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} ≤
        2 * exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
      intro x
      have h := MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le
        (h_indep x) (hmeas x) (hY x) hε
      have havg : (1 / n : ℝ) * ∑ i, μ[Y x i] = C x := by
        have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        simp only [hC x, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      rwa [havg] at h
    have hset : {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} =
        ⋃ x, {ω | ε ≤ |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} := by
      ext ω
      simp [Finset.le_sup'_iff]
    rw [hset]
    calc _ ≤ ∑ x, μ.real {ω | ε ≤ |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ _x : X, 2 * exp (-2 * n * ε ^ 2 / (b - a) ^ 2) :=
          Finset.sum_le_sum fun x _ => hone x
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  · obtain ⟨xstar, -, hxstar⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty C
    have hdev : ∀ x, |(1 / n : ℝ) * ∑ i, Y x i ω - C x| ≤ Finset.univ.sup'
        Finset.univ_nonempty (fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|) := fun x =>
      Finset.le_sup' (fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|) (Finset.mem_univ x)
    have h := CSLibExt.MachineLearning.GeneralizationBounds.risk_le_add_two_mul_of_forall_abs_sub_le
      (R := C) (Rhat := fun x => (1 / n : ℝ) * ∑ i, Y x i ω) hmin hdev xstar
    rw [hxstar]
    linarith

end Cslib.Algorithms.Simulation.SelectBest
