/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.UnitIntervalMoments
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.MeasureTheory.Measure.Prokhorov
import MathlibExt.Probability.InfiniteMixtureLimit

/-!
# Pitman's representation of consistent merger rates (existence)

A family of rates `r b k` (`2 ≤ k ≤ b`: the rate at which a given set of `k` among `b` blocks
merges) is **consistent** if `r b k = r (b + 1) k + r (b + 1) (k + 1)`. Pitman (1999,
Theorem 1) showed that the consistent families of nonnegative rates are exactly the families
`λ_{b,k} = ∫ x ^ (k - 2) (1 - x) ^ (b - k) Λ(dx)` for a finite measure `Λ` on `[0, 1]`
(`MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.mergerRate`), and that
`Λ` is unique.

Consistency and uniqueness are proved in
`Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent`
(`mergerRate_consistent`, `mergerRate_nonneg`, `eq_of_mergerRate_eq`). The existence half
proved here is a Hausdorff moment problem: consistency gives
`r (i + 2 + c) (i + 2) = ((I - E) ^ c m) i` for the sequence `m i = r (i + 2) (i + 2)` and the
shift `E`, so nonnegativity says that `m` is completely monotone, and Hausdorff's theorem
yields a finite measure on `[0, 1]` whose moments are `m`. The one-dimensional case of
`MathlibExt.Analysis.HausdorffMomentsWanted.Analysis.hausdorff_positivity` would therefore
give this statement. Here the proof constructs the measure as a weak cluster point of the
binomially weighted rows, whose factorial moments are determined by consistency.

Sources: J. Pitman, "Coalescents with multiple collisions", Ann. Probab. 27 (1999)
1870–1902, Theorem 1; F. Hausdorff, "Summationsmethoden und Momentfolgen I", Math. Z. 9
(1921) 74–109; W. Feller, *An Introduction to Probability Theory and Its Applications*,
vol. II, 2nd ed. (1971), §VII.3.
-/

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted

open MeasureTheory unitInterval Finset Filter
open scoped Topology NNReal

/- Write the rates in exponent coordinates, so that consistency is the Pascal recurrence. -/
private theorem sum_row (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, w a b = w a (b + 1) + w (a + 1) b) (a n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) * w (a + j) (n - j) = w a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_choose_succ_mul (fun j b => w (a + j) b), ← sum_add_distrib, ← ih]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by simpa using hj
    rw [show n + 1 - j = n - j + 1 by omega, ← mul_add, ← Nat.add_assoc, ← hw]

private def weight (w : ℕ → ℕ → ℝ) (n j : ℕ) : ℝ := (n.choose j : ℝ) * w j (n - j)

/- The falling factorial of order a selects a shifted row of the same triangle. -/
private theorem factorial_moment (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, w a b = w a (b + 1) + w (a + 1) b) {a n : ℕ} (ha : a ≤ n) :
    ∑ j ∈ range (n + 1), weight w n j * (j.descFactorial a : ℝ) =
      (n.descFactorial a : ℝ) * w a 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_assoc, sum_range_add]
  have low : ∑ j ∈ range a, weight w (a + m) j * (j.descFactorial a : ℝ) = 0 :=
    sum_eq_zero fun j hj => by simp [Nat.descFactorial_of_lt (mem_range.mp hj)]
  rw [low, zero_add, ← sum_row w hw a m, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hc := Nat.choose_mul (n := a + m) (k := a + j) (s := a) (by omega)
  simp only [Nat.add_sub_cancel_left] at hc
  simp only [weight, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    show a + m - (a + j) = m - j by omega]
  have hc' := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hc'
  linear_combination (a.factorial : ℝ) * w (a + j) (m - j) * hc'

private noncomputable def rowMeasure (w : ℕ → ℕ → ℝ) (n : ℕ) : FiniteMeasure I :=
  ⟨∑ j : Fin (n + 1), (weight w n j).toNNReal • Measure.dirac (bernstein.z j),
    inferInstance⟩

private theorem integral_row (w : ℕ → ℕ → ℝ) (hn : ∀ a b, 0 ≤ w a b)
    (n : ℕ) (f : C(I, ℝ)) :
    ∫ x, f x ∂(rowMeasure w n) =
      ∑ j : Fin (n + 1), weight w n j * f (bernstein.z j) := by
  change ∫ x, f x ∂(∑ j : Fin (n + 1), _) = _
  rw [integral_finsetSum_measure]
  · refine sum_congr rfl fun j _ => ?_
    have hp : 0 ≤ weight w n j := mul_nonneg (Nat.cast_nonneg _) (hn _ _)
    simp [NNReal.smul_def, Real.coe_toNNReal _ hp]
  · intro j _
    exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- Convert ordinary powers to falling factorials before passing to the limit. -/
private theorem power_moment (w : ℕ → ℕ → ℝ) (hn : ∀ a b, 0 ≤ w a b)
    (hw : ∀ a b, w a b = w a (b + 1) + w (a + 1) b) {a n : ℕ} (ha : a ≤ n) :
    ∫ x : I, (x : ℝ) ^ a ∂(rowMeasure w n) =
      ∑ s ∈ range (a + 1), ((a.stirlingSecond s : ℝ) * w s 0) *
        ((n.descFactorial s : ℝ) / (n : ℝ) ^ a) := by
  let f : C(I, ℝ) := ⟨fun x => (x : ℝ) ^ a, by fun_prop⟩
  change ∫ x, f x ∂(rowMeasure w n) = _
  rw [integral_row w hn n f]
  change ∑ j : Fin (n + 1), weight w n j * (((j : ℕ) : ℝ) / n) ^ a = _
  rw [Fin.sum_univ_eq_sum_range (fun j => weight w n j * ((j : ℝ) / n) ^ a)]
  have grid (j : ℕ) : ((j : ℝ) / n) ^ a =
      (∑ s ∈ range (a + 1), (a.stirlingSecond s : ℝ) * j.descFactorial s) / (n : ℝ) ^ a := by
    rw [div_pow]
    congr 1
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial j a
  simp_rw [grid, sum_div, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s hs => ?_
  have hsn := (Nat.le_of_lt_succ (mem_range.mp hs)).trans ha
  calc
    _ = ((a.stirlingSecond s : ℝ) / (n : ℝ) ^ a) *
        ∑ j ∈ range (n + 1), weight w n j * (j.descFactorial s : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    _ = _ := by rw [factorial_moment w hw hsn]; ring

private theorem tendsto_power_moment (w : ℕ → ℕ → ℝ) (hn : ∀ a b, 0 ≤ w a b)
    (hw : ∀ a b, w a b = w a (b + 1) + w (a + 1) b) (a : ℕ) :
    Tendsto (fun n => ∫ x : I, (x : ℝ) ^ a ∂(rowMeasure w n)) atTop (𝓝 (w a 0)) := by
  let term (n s : ℕ) := ((a.stirlingSecond s : ℝ) * w s 0) *
    ((n.descFactorial s : ℝ) / (n : ℝ) ^ a)
  have lower (s : ℕ) (hs : s ∈ range a) : Tendsto (fun n => term n s) atTop (𝓝 0) := by
    have hpow := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (mem_range.mp hs)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hfall := MathlibExt.Probability.InfiniteMixtureLimit.tendsto_descFactorial_div_pow s
    have h := (hfall.mul hpow).const_mul ((a.stirlingSecond s : ℝ) * w s 0)
    refine (by simpa using h : Tendsto _ atTop (𝓝 (0 : ℝ))).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn'
    dsimp [term, Function.comp_def]
    field_simp
  have last : Tendsto (fun n => term n a) atTop (𝓝 (w a 0)) := by
    simpa [term, Nat.stirlingSecond_self] using
      (MathlibExt.Probability.InfiniteMixtureLimit.tendsto_descFactorial_div_pow a).const_mul
        (w a 0)
  have hsum := (tendsto_finsetSum (range a) lower).add last
  refine (by simpa using hsum : Tendsto _ atTop (𝓝 (w a 0))).congr' ?_
  filter_upwards [eventually_ge_atTop a] with n hna
  simpa [sum_range_succ, term] using (power_moment w hn hw hna).symm

private theorem represents_triangle (w : ℕ → ℕ → ℝ) (hn : ∀ a b, 0 ≤ w a b)
    (hw : ∀ a b, w a b = w a (b + 1) + w (a + 1) b) :
    ∃ μ : FiniteMeasure I, ∀ a b, w a b = unitIntervalMoment μ a b := by
  let mass : ℝ≥0 := ⟨w 0 0, hn _ _⟩
  have hmass (n : ℕ) : (rowMeasure w n).mass = mass := by
    apply NNReal.eq
    rw [FiniteMeasure.mass, ← FiniteMeasure.measureReal_eq_coe_coeFn]
    change _ = w 0 0
    have h := power_moment w hn hw (a := 0) (Nat.zero_le n)
    simpa only [pow_zero, integral_const, smul_eq_mul, mul_one, Nat.zero_add, sum_range_one,
      Nat.stirlingSecond_self, Nat.cast_one, one_mul, Nat.descFactorial_zero, div_one] using h
  obtain ⟨μ, _, hμ⟩ := (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace I mass)
    |>.exists_mapClusterPt (u := rowMeasure w) (f := atTop)
      (le_principal_iff.mpr <| eventually_map.mpr <| Eventually.of_forall hmass)
  refine ⟨μ, fun a b => ?_⟩
  induction b generalizing a with
  | zero =>
    let f : C(I, ℝ) := ⟨fun x => (x : ℝ) ^ a, by fun_prop⟩
    have hc := hμ.continuousAt_comp (FiniteMeasure.continuous_integral_continuousMap f).continuousAt
    have hlim := tendsto_power_moment w hn hw a
    have heq : ∫ x, f x ∂μ = w a 0 := eq_of_nhds_neBot (hc.clusterPt.mono hlim)
    simpa [unitIntervalMoment, f] using heq.symm
  | succ b ih =>
    linarith only [hw a b, ih a, ih (a + 1), unitIntervalMoment_rec (μ : Measure I) a b]

/-- **Pitman's representation theorem, existence half** (Pitman 1999, Theorem 1): every
consistent family of nonnegative merger rates `r b k`, `2 ≤ k ≤ b`, is the family of merger
rates `λ_{b,k}` of some finite measure `Λ` on `[0, 1]`. (Uniqueness of `Λ` is
`LambdaCoalescent.eq_of_mergerRate_eq`.)

Source: Pitman (1999), Theorem 1; Hausdorff (1921). -/
public theorem exists_measure_of_consistent (r : ℕ → ℕ → ℝ)
    (hnonneg : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ r b k)
    (hcons : ∀ b k, 2 ≤ k → k ≤ b → r b k = r (b + 1) k + r (b + 1) (k + 1)) :
    ∃ (Λ : Measure I) (_ : IsFiniteMeasure Λ), ∀ b k, 2 ≤ k → k ≤ b →
      r b k = unitIntervalMoment Λ (k - 2) (b - k) := by
  let w (a b : ℕ) := r (a + b + 2) (a + 2)
  have hn (a b : ℕ) : 0 ≤ w a b := hnonneg _ _ (by omega) (by omega)
  have hw (a b : ℕ) : w a b = w a (b + 1) + w (a + 1) b := by
    simpa [w, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hcons (a + b + 2) (a + 2) (by omega) (by omega)
  obtain ⟨μ, hμ⟩ := represents_triangle w hn hw
  refine ⟨μ, inferInstance, fun b k hk hkb => ?_⟩
  simpa [w, show k - 2 + (b - k) + 2 = b by omega, Nat.sub_add_cancel hk] using
    hμ (k - 2) (b - k)

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted
