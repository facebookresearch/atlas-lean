/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Permutation (group-invariance) p-values are valid

Let a finite group `G` act on the sample space `Ω` and let the null law `μ` be invariant under
`G` (`SMulInvariantMeasure G Ω μ`); permutations of exchangeable observations and sign flips of
symmetric ones are the standard examples. For a test statistic `T : Ω → ℝ`, the permutation
p-value is the fraction of the orbit at least as extreme as the observed statistic,
`p(ω) = #{g ∈ G | T(g • ω) ≥ T(ω)} / |G|`.

## Main results

* `card_filter_rankCount_le`: for any `t : G → ℝ`, at most `k` elements `h` have
  `#{g | t h ≤ t g} ≤ k` (a deterministic counting lemma).
* `isValidPValue_permutationPValue`: the permutation p-value is valid,
  `μ {p ≤ α} ≤ α` for every `α ∈ [0, 1]` (Lehmann and Romano 2005, §15.2;
  Hemerik and Goeman 2018).

The version with `B` random group elements, `p = (1 + #{b | T(g_b • ω) ≥ T(ω)}) / (B + 1)`
(Phipson and Smyth 2010), is `isValidPValue_monteCarloPermutationPValue` in
`MathlibExt/Probability/Statistics/MultipleTesting/MonteCarloPermutationPValue.lean`.

## References

* J. Hemerik and J. Goeman, *Exact testing with random permutations*, TEST 27 (2018),
  811–825.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §15.2.
* B. Phipson and G. K. Smyth, *Permutation p-values should never be zero*, Stat. Appl. Genet.
  Mol. Biol. 9 (2010), Article 39.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (G : Type*) [Group G] [Fintype G] [MulAction G Ω]

/-- The permutation (group-invariance) p-value of the statistic `T` at `ω`: the fraction of
group elements `g` with `T (g • ω) ≥ T ω`. -/
noncomputable def permutationPValue (T : Ω → ℝ) (ω : Ω) : ℝ :=
  ((Finset.univ.filter fun g : G => T ω ≤ T (g • ω)).card : ℝ) / Fintype.card G

omit [Group G] in
/-- Counting lemma: for any family of reals `t` indexed by `G` and any `k`, at most `k`
elements `h` have rank count `#{g | t h ≤ t g}` at most `k`. -/
theorem card_filter_rankCount_le (t : G → ℝ) (k : ℕ) :
    (Finset.univ.filter fun h : G =>
        (Finset.univ.filter fun g : G => t h ≤ t g).card ≤ k).card ≤ k := by
  set S := Finset.univ.filter fun h : G =>
    (Finset.univ.filter fun g : G => t h ≤ t g).card ≤ k
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  obtain ⟨h₀, hh₀, hmin⟩ := S.exists_min_image t hS
  refine le_trans (Finset.card_le_card fun h hh => ?_) (Finset.mem_filter.1 hh₀).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hmin h hh

variable {G}

omit [MeasurableSpace Ω] in
/-- Reindexing the orbit: the p-value at `h • ω` counts the orbit of `ω` against `T (h • ω)`. -/
private theorem card_filter_smul (T : Ω → ℝ) (ω : Ω) (h : G) :
    (Finset.univ.filter fun g : G => T (h • ω) ≤ T (g • h • ω)).card =
      (Finset.univ.filter fun g : G => T (h • ω) ≤ T (g • ω)).card := by
  refine Finset.card_bij (fun g _ => g * h) (fun g hg => ?_) (fun a _ b _ hab => ?_)
    (fun g hg => ⟨g * h⁻¹, ?_, by simp⟩)
  · simpa [mul_smul] using hg
  · simpa using hab
  · simpa [mul_smul] using hg

private theorem measurable_permutationPValue (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω)
    {T : Ω → ℝ} (hT : Measurable T) : Measurable (permutationPValue G T) := by
  have h : ∀ ω, ((Finset.univ.filter fun g : G => T ω ≤ T (g • ω)).card : ℝ) =
      ∑ g : G, Set.indicator {ω | T ω ≤ T (g • ω)} (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp [Set.indicator_apply, Finset.sum_boole]
  unfold permutationPValue
  simp_rw [h]
  refine Measurable.div_const (Finset.measurable_sum _ fun g _ => ?_) _
  exact measurable_const.indicator (measurableSet_le hT (hT.comp (hsmul g)))

/-- Lehmann and Romano (2005), §15.2; Hemerik and Goeman (2018): if the law `μ` is invariant
under the action of a finite group `G`, the permutation p-value of any measurable statistic is
valid. -/
theorem isValidPValue_permutationPValue (μ : Measure Ω) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G Ω μ] (hsmul : ∀ g : G, Measurable fun ω : Ω => g • ω)
    {T : Ω → ℝ} (hT : Measurable T) :
    IsValidPValue μ (permutationPValue G T) := by
  intro α hα
  set N := Fintype.card G
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  set S := {ω | permutationPValue G T ω ≤ α}
  have hS : MeasurableSet S :=
    measurableSet_le (measurable_permutationPValue hsmul hT) measurable_const
  have hSh : ∀ h : G, MeasurableSet ((fun ω => h • ω) ⁻¹' S) := fun h => hsmul h hS
  -- pointwise: few group elements move `ω` into the rejection region
  have hpt : ∀ ω,
      (∑ h : G, ((fun ω => h • ω) ⁻¹' S).indicator (fun _ => (1 : ENNReal)) ω : ENNReal) ≤
      ENNReal.ofReal (α * N) := by
    intro ω
    have hcount : (Finset.univ.filter fun h : G => h • ω ∈ S).card ≤ ⌊α * N⌋₊ := by
      refine le_trans (Finset.card_le_card fun h hh => ?_)
        (card_filter_rankCount_le G (fun g => T (g • ω)) ⌊α * N⌋₊)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, Set.mem_ofPred_eq,
        permutationPValue, card_filter_smul] at hh ⊢
      rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)] at hh
      exact Nat.le_floor hh
    calc (∑ h : G, ((fun ω => h • ω) ⁻¹' S).indicator (fun _ => (1 : ENNReal)) ω : ENNReal)
        = ((Finset.univ.filter fun h : G => h • ω ∈ S).card : ENNReal) := by
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun h _ => ?_
          by_cases hh : h • ω ∈ S <;> simp [hh]
      _ ≤ (⌊α * N⌋₊ : ENNReal) := by exact_mod_cast hcount
      _ ≤ ENNReal.ofReal (α * N) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.floor_le (mul_nonneg hα.1 hN.le))
  have hsum : (N : ENNReal) * μ S =
      ∫⁻ ω, ∑ h : G, ((fun ω => h • ω) ⁻¹' S).indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
    rw [lintegral_finsetSum _ fun h _ => (measurable_const.indicator (hSh h))]
    simp_rw [lintegral_indicator_const (hSh _), one_mul,
      SMulInvariantMeasure.measure_preimage_smul _ hS]
    simp [N]
  have hle : (N : ENNReal) * μ S ≤ (N : ENNReal) * ENNReal.ofReal α := by
    rw [hsum]
    calc ∫⁻ ω, ∑ h : G, ((fun ω => h • ω) ⁻¹' S).indicator (fun _ => (1 : ENNReal)) ω ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (α * N) ∂μ := lintegral_mono hpt
      _ = (N : ENNReal) * ENNReal.ofReal α := by
          rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_mul hα.1,
            ENNReal.ofReal_natCast, mul_comm]
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)).1
    hle

end MathlibExt.Probability.Statistics.MultipleTesting
