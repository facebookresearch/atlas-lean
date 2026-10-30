/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Data.Matrix.Mul
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass
import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman

/-!
# Λ-coalescents: Pitman's merger rates and their consistency

A **Λ-coalescent** (Pitman 1999; Sagitov 1999) is an exchangeable coalescent in which many
blocks may merge at once. It is parametrized by a finite measure `Λ` on `[0, 1]`, which we take
as a measure on `unitInterval` (every definition below requires `[IsFiniteMeasure Λ]`). While
there are `b` blocks, each particular set of `k` of them (`2 ≤ k ≤ b`) merges into one block at
rate

`λ_{b,k} = ∫ x ^ (k - 2) * (1 - x) ^ (b - k) Λ(dx)`

(with `0 ^ 0 = 1`, so an atom of `Λ` at `0` contributes only to binary mergers `k = 2`). The
total rate at which some merger happens is `λ_b = ∑_{k=2}^b (b.choose k) λ_{b,k}`, and the
number of blocks jumps from `b` to `b - k + 1` at rate `(b.choose k) λ_{b,k}`.

This file is about these rates; it does not construct the partition-valued process.

## Main definitions

* `LambdaCoalescent.mergerRate Λ b k`: Pitman's rate `λ_{b,k}`, defined to be `0` unless
  `2 ≤ k ≤ b`.
* `LambdaCoalescent.totalMergerRate Λ b`: the total merger rate `λ_b`.
* `LambdaCoalescent.blockCountingGenerator Λ n`: the generator of the block-counting process
  on the states `0, …, n` (state `b` = `b` blocks).

## Main results

* `mergerRate_consistent`: **Pitman's consistency relation**
  `λ_{b,k} = λ_{b+1,k} + λ_{b+1,k+1}` for `2 ≤ k ≤ b` (Pitman 1999; Berestycki 2009, §3.1).
* `mergerRate_nonneg`, `mergerRate_le_measure_univ`, `mergerRate_two_two`: the rates are
  nonnegative, bounded by the total mass, and two blocks merge at rate `Λ [0, 1]`.
* `totalMergerRate_eq`: `λ_b = (b.choose 2) Λ {0} +
  ∫_{(0,1]} (1 - (1 - x) ^ b - b x (1 - x) ^ (b - 1)) / x ^ 2 Λ(dx)`.
* `totalMergerRate_succ`, `totalMergerRate_mono`: `λ_{b+1} = λ_b + b λ_{b+1,2}`, so `λ_b` is
  nondecreasing in `b`.
* `isRateMatrix_blockCountingGenerator`: the block-counting generator is a rate matrix.
* `mergerRate_dirac_zero`, `totalMergerRate_dirac_zero`: Kingman's coalescent (`Λ = δ₀`):
  only binary mergers, at rate `1` per pair, so `λ_b = b.choose 2`.
* `mergerRate_volume`, `totalMergerRate_volume`: the Bolthausen–Sznitman coalescent
  (`Λ` = uniform): `λ_{b,k} = (k - 2)! (b - k)! / (b - 1)!` and `λ_b = b - 1`.
* `eq_of_mergerRate_eq`: `Λ` is determined by its rates (indeed by the `λ_{k,k}`, which are
  the moments of `Λ`): the uniqueness half of Pitman's representation theorem. The existence
  half (every consistent family of nonnegative rates comes from some `Λ`, a Hausdorff moment
  problem) is recorded as wanted in
  `WantedExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted`.

## References

* J. Pitman, *Coalescents with multiple collisions*, Ann. Probab. 27 (1999), 1870–1902.
* S. Sagitov, *The general coalescent with asynchronous mergers of ancestral lines*,
  J. Appl. Probab. 36 (1999), 1116–1125.
* E. Bolthausen, A.-S. Sznitman, *On Ruelle's probability cascades and an abstract cavity
  method*, Comm. Math. Phys. 197 (1998), 247–276.
* N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16 (2009), §3.1.
-/

@[expose] public section

open MeasureTheory Finset unitInterval

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

variable (Λ : Measure I)

/- Every definition requires `Λ` to be finite: for an infinite-mass measure the Bochner integrals
below would take Lean's junk value `0` (for example, `Λ = ⊤` would get pair rate `0`). -/

/-- **Pitman's merger rate** `λ_{b,k} = ∫ x ^ (k - 2) (1 - x) ^ (b - k) Λ(dx)`: while there are
`b` blocks, the rate at which a given set of `k` of them merges into one block, for
`2 ≤ k ≤ b` (Pitman 1999, Theorem 1; Sagitov 1999). Powers are natural-number powers, so
`0 ^ 0 = 1`. Outside `2 ≤ k ≤ b` no such merger exists, and the rate is defined to be `0`. -/
def mergerRate [IsFiniteMeasure Λ] (b k : ℕ) : ℝ :=
  if 2 ≤ k ∧ k ≤ b then ∫ x, (x : ℝ) ^ (k - 2) * (1 - (x : ℝ)) ^ (b - k) ∂Λ else 0

/-- The **total merger rate** `λ_b = ∑_{k=2}^b (b.choose k) λ_{b,k}` while there are `b`
blocks (Pitman 1999; Berestycki 2009, §3.1). -/
def totalMergerRate [IsFiniteMeasure Λ] (b : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 b, (b.choose k : ℝ) * mergerRate Λ b k

/-- The generator of the **block-counting process** of the Λ-coalescent on the states
`0, …, n` (state `b` means `b` blocks): from `b` blocks the process jumps to `j < b` blocks at
rate `(b.choose (b + 1 - j)) λ_{b, b + 1 - j}` (a `(b + 1 - j)`-merger), and the diagonal is
`-λ_b`. States `0` and `1` are absorbing (state `0` is never reached from `b ≥ 1`). -/
def blockCountingGenerator [IsFiniteMeasure Λ] (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  if i = j then -totalMergerRate Λ i
  else if (j : ℕ) < i then ((i : ℕ).choose (i + 1 - j) : ℝ) * mergerRate Λ i (i + 1 - j)
  else 0

variable [IsFiniteMeasure Λ]

/-- The merger rate inside its domain. -/
theorem mergerRate_of_le {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    mergerRate Λ b k = ∫ x, (x : ℝ) ^ (k - 2) * (1 - (x : ℝ)) ^ (b - k) ∂Λ := by
  simp [mergerRate, hk, hkb]

/-- Merger rates are nonnegative. -/
theorem mergerRate_nonneg (b k : ℕ) : 0 ≤ mergerRate Λ b k := by
  unfold mergerRate
  split_ifs
  · exact integral_nonneg fun x => mul_nonneg (pow_nonneg (nonneg x) _)
      (pow_nonneg (one_sub_nonneg x) _)
  · exact le_rfl

/-- Two blocks merge at rate `Λ [0, 1]`; `Λ` is often normalized to a probability measure,
so that this pair rate is `1` as in Kingman's coalescent. -/
theorem mergerRate_two_two : mergerRate Λ 2 2 = Λ.real Set.univ := by
  simp [mergerRate]

/-- The total merger rate is nonnegative. -/
theorem totalMergerRate_nonneg (b : ℕ) : 0 ≤ totalMergerRate Λ b := by
  exact sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (mergerRate_nonneg Λ b k)

/-- The block-counting generator is a rate matrix: its jump rates are nonnegative and each
row sums to `0`, since the jump rates out of `b` blocks add up to `λ_b`. -/
theorem isRateMatrix_blockCountingGenerator (n : ℕ) :
    ProbabilityTheory.IsRateMatrix (blockCountingGenerator Λ n) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [blockCountingGenerator, ite_eq_right hij]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (mergerRate_nonneg Λ _ _)
    · exact le_rfl
  · set g : ℕ → ℝ := fun m => ((i : ℕ).choose (i + 1 - m) : ℝ) * mergerRate Λ i (i + 1 - m)
    have hF : ∀ j : Fin (n + 1), blockCountingGenerator Λ n i j =
        (if (i : ℕ) = j then -totalMergerRate Λ i else 0) + (if (j : ℕ) < i then g j else 0) := by
      intro j
      simp only [blockCountingGenerator, Fin.ext_iff]
      split_ifs <;> first | omega | simp [g]
    simp_rw [hF]
    rw [Fin.sum_univ_eq_sum_range (fun m => (if (i : ℕ) = m then -totalMergerRate Λ i else 0) +
      (if m < i then g m else 0)) (n + 1), sum_add_distrib, sum_ite_eq,
      ite_eq_left (mem_range.2 i.2), ← sum_filter,
      show (range (n + 1)).filter (· < (i : ℕ)) = range i by
        ext m; simp only [mem_filter, mem_range]; omega]
    suffices h : ∑ m ∈ range i, g m = totalMergerRate Λ i by linarith
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · simp [h0, totalMergerRate]
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hpos]
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0, zero_add, totalMergerRate]
    refine sum_nbij' (fun m => i + 1 - m) (fun k => i + 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [mem_Ico, mem_Icc] at hm ⊢; omega
    · intro k hk; simp only [mem_Ico, mem_Icc] at hk ⊢; omega
    · intro m hm; simp only [mem_Ico] at hm; omega
    · intro k hk; simp only [mem_Icc] at hk; omega
    · intro m _; rfl


/-- The integrand `x ^ a (1 - x) ^ c` lies in `[0, 1]` on `[0, 1]`. -/
private lemma pow_mul_one_sub_pow_mem (a c : ℕ) (x : I) :
    0 ≤ (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c ∧ (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c ≤ 1 :=
  ⟨mul_nonneg (pow_nonneg (nonneg x) _) (pow_nonneg (one_sub_nonneg x) _),
    (mul_le_of_le_one_left (pow_nonneg (one_sub_nonneg x) _)
      (pow_le_one₀ (nonneg x) (le_one x))).trans
      (pow_le_one₀ (one_sub_nonneg x) (one_sub_le_one x))⟩

/-- The integrand `x ^ a (1 - x) ^ c` is integrable against a finite measure on `[0, 1]`. -/
private lemma integrable_pow_mul_one_sub_pow (a c : ℕ) :
    Integrable (fun x : I => (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c) Λ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) (ae_of_all _ fun x => ?_)
  obtain ⟨h0, h1⟩ := pow_mul_one_sub_pow_mem a c x
  rwa [Real.norm_eq_abs, abs_of_nonneg h0]

/-- A merger rate is at most the total mass of `Λ`. -/
theorem mergerRate_le_measure_univ (b k : ℕ) : mergerRate Λ b k ≤ Λ.real Set.univ := by
  unfold mergerRate
  split_ifs
  · calc ∫ x, (x : ℝ) ^ (k - 2) * (1 - (x : ℝ)) ^ (b - k) ∂Λ ≤ ∫ _x, (1 : ℝ) ∂Λ :=
          integral_mono (integrable_pow_mul_one_sub_pow Λ _ _) (integrable_const _)
            fun x => (pow_mul_one_sub_pow_mem _ _ x).2
      _ = Λ.real Set.univ := by simp
  · exact measureReal_nonneg

/-- **Pitman's consistency relation** `λ_{b,k} = λ_{b+1,k} + λ_{b+1,k+1}` for `2 ≤ k ≤ b`
(Pitman 1999; Berestycki 2009, §3.1): a given `k`-set of `b` blocks merges, with an extra
block present, either without it or together with it. -/
theorem mergerRate_consistent {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    mergerRate Λ b k = mergerRate Λ (b + 1) k + mergerRate Λ (b + 1) (k + 1) := by
  rw [mergerRate_of_le Λ hk hkb, mergerRate_of_le Λ hk (by omega),
    mergerRate_of_le Λ (by omega) (by omega),
    ← integral_add (integrable_pow_mul_one_sub_pow Λ _ _) (integrable_pow_mul_one_sub_pow Λ _ _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, b = i + 2 + j := ⟨b - (i + 2), by omega⟩
  simp only [show i + 2 - 2 = i by omega, show i + 2 + 1 - 2 = i + 1 by omega,
    show i + 2 + j - (i + 2) = j by omega, show i + 2 + j + 1 - (i + 2) = j + 1 by omega,
    show i + 2 + j + 1 - (i + 2 + 1) = j by omega]
  ring

/-- The polynomial identity behind the closed form of the total merger rate:
`x ^ 2 ∑_{k=2}^b (b.choose k) x ^ (k - 2) (1 - x) ^ (b - k) = 1 - (1 - x) ^ b -
b x (1 - x) ^ (b - 1)` for every real `x` and every `b` (binomial theorem). -/
theorem sq_mul_sum_choose_mul_pow (x : ℝ) (b : ℕ) :
    x ^ 2 * ∑ k ∈ Icc 2 b, (b.choose k : ℝ) * (x ^ (k - 2) * (1 - x) ^ (b - k)) =
      1 - (1 - x) ^ b - b * x * (1 - x) ^ (b - 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h := add_pow x (1 - x) b
  rw [add_sub_cancel, one_pow, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega),
    sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_add_one_right_eq_Icc] at h
  rw [mul_sum]
  have hs : ∑ k ∈ Icc 2 b, x ^ 2 * ((b.choose k : ℝ) * (x ^ (k - 2) * (1 - x) ^ (b - k))) =
      ∑ k ∈ Icc 2 b, x ^ k * (1 - x) ^ (b - k) * (b.choose k : ℝ) := by
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := (mem_Icc.1 hk).1; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hs]
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, zero_add] at h
  linarith

/-- The integrand of the total merger rate,
`∑_{k=2}^b (b.choose k) x ^ (k - 2) (1 - x) ^ (b - k)` (a polynomial in `x`). -/
private def rateKernel (b : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 b, (b.choose k : ℝ) * (x ^ (k - 2) * (1 - x) ^ (b - k))

/-- At `x = 0` only binary mergers survive: the kernel is `b.choose 2`. -/
private lemma rateKernel_zero (b : ℕ) : rateKernel b 0 = b.choose 2 := by
  rcases lt_or_ge b 2 with hb | hb
  · simp [rateKernel, Icc_eq_empty (show ¬ 2 ≤ b by omega), Nat.choose_eq_zero_of_lt hb]
  · simp only [rateKernel, sub_zero, one_pow, mul_one]
    rw [sum_eq_single_of_mem 2 (mem_Icc.2 ⟨le_rfl, hb⟩) fun k hk hk2 => by
      simp [show k - 2 ≠ 0 by have := (mem_Icc.1 hk).1; omega]]
    simp

/-- The total merger rate is the integral of the kernel. -/
private lemma totalMergerRate_eq_integral (b : ℕ) :
    totalMergerRate Λ b = ∫ x, rateKernel b (x : ℝ) ∂Λ := by
  unfold rateKernel
  rw [totalMergerRate, integral_finsetSum _ fun k _ =>
    (integrable_pow_mul_one_sub_pow Λ _ _).const_mul _]
  refine sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, mergerRate_of_le Λ (mem_Icc.1 hk).1 (mem_Icc.1 hk).2]

/-- The kernel is integrable. -/
private lemma integrable_rateKernel (b : ℕ) :
    Integrable (fun x : I => rateKernel b (x : ℝ)) Λ :=
  integrable_finsetSum _ fun _ _ => (integrable_pow_mul_one_sub_pow Λ _ _).const_mul _

/-- **The total merger rate in closed form** (Berestycki 2009, §3.1):
`λ_b = (b.choose 2) Λ {0} + ∫_{(0,1]} (1 - (1 - x) ^ b - b x (1 - x) ^ (b - 1)) / x ^ 2 Λ(dx)`.
The atom at `0` (the Kingman part) is split off, so no division by `0` occurs. -/
theorem totalMergerRate_eq (b : ℕ) :
    totalMergerRate Λ b = (b.choose 2 : ℝ) * Λ.real {0} +
      ∫ x in ({0}ᶜ : Set I),
        (1 - (1 - (x : ℝ)) ^ b - b * (x : ℝ) * (1 - (x : ℝ)) ^ (b - 1)) / (x : ℝ) ^ 2 ∂Λ := by
  rw [totalMergerRate_eq_integral,
    ← integral_add_compl (measurableSet_singleton 0) (integrable_rateKernel Λ b),
    integral_singleton, Set.Icc.coe_zero, rateKernel_zero, smul_eq_mul, mul_comm]
  congr 1
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hx0 : (x : ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [eq_div_iff (pow_ne_zero 2 hx0), mul_comm]
  exact sq_mul_sum_choose_mul_pow (x : ℝ) b

/-- One more block adds `b` to the kernel times `(1 - x) ^ (b - 1)`. -/
private lemma rateKernel_succ (b : ℕ) (x : ℝ) :
    rateKernel (b + 1) x = rateKernel b x + b * (1 - x) ^ (b - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [rateKernel_zero, rateKernel_zero, Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    simp only [sub_zero, one_pow, mul_one]
    ring
  refine mul_left_cancel₀ (pow_ne_zero 2 hx) ?_
  rw [mul_add, rateKernel, rateKernel, sq_mul_sum_choose_mul_pow, sq_mul_sum_choose_mul_pow]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- Adding a block raises the total merger rate by `b λ_{b+1,2}`:
`λ_{b+1} = λ_b + b λ_{b+1,2}`. The new events are exactly the binary mergers of the new block
with one of the `b` old ones (a consequence of the consistency relation). -/
theorem totalMergerRate_succ (b : ℕ) :
    totalMergerRate Λ (b + 1) = totalMergerRate Λ b + b * mergerRate Λ (b + 1) 2 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [totalMergerRate]
  rw [totalMergerRate_eq_integral, totalMergerRate_eq_integral,
    mergerRate_of_le Λ le_rfl (by omega), ← integral_const_mul,
    ← integral_add (integrable_rateKernel Λ b)
      ((integrable_pow_mul_one_sub_pow Λ _ _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [rateKernel_succ, show b + 1 - 2 = b - 1 by omega, Nat.sub_self, pow_zero, one_mul]

/-- The total merger rate `λ_b` is nondecreasing in the number of blocks `b`. -/
theorem totalMergerRate_mono : Monotone (totalMergerRate Λ) :=
  monotone_nat_of_le_succ fun b => by
    rw [totalMergerRate_succ]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (mergerRate_nonneg Λ _ _))

/-- **Uniqueness in Pitman's representation**: a finite measure on `[0, 1]` is determined by
its merger rates; indeed by the rates `λ_{k,k} = ∫ x ^ (k - 2) Λ(dx)` of complete mergers,
which are its moments (Pitman 1999, Theorem 1). -/
theorem eq_of_mergerRate_eq (Λ' : Measure I) [IsFiniteMeasure Λ']
    (h : ∀ k, 2 ≤ k → mergerRate Λ k k = mergerRate Λ' k k) : Λ = Λ' := by
  -- equal moments
  have hmom : ∀ j : ℕ, ∫ x, (x : ℝ) ^ j ∂Λ = ∫ x, (x : ℝ) ^ j ∂Λ' := by
    intro j
    have := h (j + 2) (by omega)
    simpa [mergerRate_of_le _ (show 2 ≤ j + 2 by omega) le_rfl] using this
  have hint : ∀ (μ : Measure I) [IsFiniteMeasure μ] (j : ℕ),
      Integrable (fun x : I => (x : ℝ) ^ j) μ := fun μ _ j => by
    simpa using integrable_pow_mul_one_sub_pow μ j 0
  -- equal integrals of polynomials
  have hpoly : ∀ p : Polynomial ℝ, ∫ x, p.eval (x : ℝ) ∂Λ = ∫ x, p.eval (x : ℝ) ∂Λ' := by
    intro p
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ fun i _ => (hint Λ i).const_mul _,
      integral_finsetSum _ fun i _ => (hint Λ' i).const_mul _]
    exact sum_congr rfl fun i _ => by rw [integral_const_mul, integral_const_mul, hmom]
  -- Weierstrass approximation
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  set M := Λ.real Set.univ + Λ'.real Set.univ + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f.toContinuousMap (ε / M)
    (div_pos hε hM0)
  set P : BoundedContinuousFunction I ℝ :=
    BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn _)
  have hPf : ∀ x : I, ‖f x - P x‖ ≤ ε / M := fun x => by
    rw [norm_sub_rev]
    exact (ContinuousMap.norm_coe_le_norm _ x).trans hp.le
  have hP : ∀ (μ : Measure I), ∫ x, P x ∂μ = ∫ x, p.eval (x : ℝ) ∂μ := fun μ => rfl
  have hbound : ∀ (μ : Measure I) [IsFiniteMeasure μ],
      ‖∫ x, f x ∂μ - ∫ x, P x ∂μ‖ ≤ ε / M * μ.real Set.univ := fun μ _ => by
    rw [← integral_sub (f.integrable μ) (P.integrable μ)]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ hPf)
  have h1 := hbound Λ
  have h2 := hbound Λ'
  rw [hP, hpoly] at h1
  rw [hP] at h2
  rw [Real.dist_eq]
  calc |∫ x, f x ∂Λ - ∫ x, f x ∂Λ'|
      ≤ ‖∫ x, f x ∂Λ - ∫ x, p.eval (x : ℝ) ∂Λ'‖ + ‖∫ x, f x ∂Λ' - ∫ x, p.eval (x : ℝ) ∂Λ'‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        have := abs_sub_le (∫ x, f x ∂Λ) (∫ x, p.eval (x : ℝ) ∂Λ') (∫ x, f x ∂Λ')
        rwa [abs_sub_comm (∫ x, p.eval (x : ℝ) ∂Λ')] at this
    _ ≤ ε / M * Λ.real Set.univ + ε / M * Λ'.real Set.univ := add_le_add h1 h2
    _ ≤ ε := by
        rw [← mul_add, div_mul_eq_mul_div, div_le_iff₀ hM0]
        nlinarith [measureReal_nonneg (μ := Λ) (s := Set.univ)]

/-! ### Kingman's coalescent: `Λ = δ₀` -/

/-- **Kingman's coalescent** is the Λ-coalescent with `Λ = δ₀`: only binary mergers occur,
each pair merging at rate `1` (Pitman 1999; Berestycki 2009, §3.1). -/
theorem mergerRate_dirac_zero (b k : ℕ) :
    mergerRate (Measure.dirac 0) b k = if k = 2 ∧ 2 ≤ b then 1 else 0 := by
  unfold mergerRate
  rw [integral_dirac]
  by_cases hk : k = 2
  · subst hk; simp
  · have : ¬ (k = 2 ∧ 2 ≤ b) := fun h => hk h.1
    rw [ite_eq_right this]
    split_ifs with h
    · simp [show k - 2 ≠ 0 by omega]
    · rfl

/-- For Kingman's coalescent the total merger rate is the number of pairs, `λ_b = b.choose 2`.
-/
theorem totalMergerRate_dirac_zero (b : ℕ) :
    totalMergerRate (Measure.dirac 0) b = b.choose 2 := by
  rw [totalMergerRate]
  simp_rw [mergerRate_dirac_zero]
  rcases lt_or_ge b 2 with hb | hb
  · rw [Icc_eq_empty (by omega), sum_empty, Nat.choose_eq_zero_of_lt hb, Nat.cast_zero]
  · rw [sum_eq_single_of_mem 2 (mem_Icc.2 ⟨le_rfl, hb⟩) fun k _ hk => by simp [hk]]
    simp [hb]

/-! ### The Bolthausen–Sznitman coalescent: `Λ` uniform on `[0, 1]` -/

/-- Integrals against Lebesgue measure on `unitInterval` are interval integrals over `[0, 1]`. -/
private lemma integral_unitInterval (f : ℝ → ℝ) :
    ∫ x : I, f x = ∫ x in (0 : ℝ)..1, f x := by
  rw [(unitInterval.measurePreserving_coe).integral_comp
    (MeasurableEmbedding.subtype_coe measurableSet_Icc), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

/-- The Beta integral at natural arguments, `∫₀¹ x ^ a (1 - x) ^ c dx = a! c! / (a + c + 1)!`,
by induction on `c` through `x ^ a (1 - x) ^ (c + 1) = x ^ a (1 - x) ^ c - x ^ (a + 1) (1 - x) ^ c`
(the consistency relation for the uniform measure). -/
private lemma integral_pow_mul_one_sub_pow (c : ℕ) : ∀ a : ℕ,
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ c =
      (a.factorial * c.factorial : ℝ) / (a + c + 1).factorial := by
  induction c with
  | zero =>
    intro a
    simp only [pow_zero, mul_one, integral_pow, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  | succ c ih =>
    intro a
    have h : ∀ x : ℝ,
        x ^ a * (1 - x) ^ (c + 1) = x ^ a * (1 - x) ^ c - x ^ (a + 1) * (1 - x) ^ c :=
      fun x => by ring
    simp_rw [h]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _), ih a, ih (a + 1),
      show a + 1 + c + 1 = (a + c + 1) + 1 by ring,
      show a + (c + 1) + 1 = (a + c + 1) + 1 by ring,
      Nat.factorial_succ (a + c + 1), Nat.factorial_succ a, Nat.factorial_succ c]
    have h1 : ((a + c + 1).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The **Bolthausen–Sznitman coalescent** (`Λ` = Lebesgue measure on `[0, 1]`) has merger
rates given by the Beta integral `λ_{b,k} = (k - 2)! (b - k)! / (b - 1)!` for `2 ≤ k ≤ b`
(Bolthausen–Sznitman 1998; Pitman 1999; Berestycki 2009, §3.1). -/
theorem mergerRate_volume {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    mergerRate volume b k =
      ((k - 2).factorial * (b - k).factorial : ℝ) / (b - 1).factorial := by
  rw [mergerRate_of_le _ hk hkb,
    integral_unitInterval (fun y => y ^ (k - 2) * (1 - y) ^ (b - k)),
    integral_pow_mul_one_sub_pow, show k - 2 + (b - k) + 1 = b - 1 by omega]

/-- For the Bolthausen–Sznitman coalescent the total merger rate is `λ_b = b - 1` (`b ≥ 1`). -/
theorem totalMergerRate_volume {b : ℕ} (hb : 1 ≤ b) :
    totalMergerRate volume b = b - 1 := by
  have hterm : ∀ k ∈ Icc 2 b, (b.choose k : ℝ) * mergerRate volume b k =
      (b : ℝ) / 2 * ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
    intro k hk
    obtain ⟨hk2, hkb⟩ := mem_Icc.1 hk
    rw [mergerRate_volume hk2 hkb, Nat.cast_choose_two]
    have hc : ((b.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * ((b - k).factorial : ℝ) =
        (b.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkb
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ] at hc
    simp only [Nat.add_sub_cancel] at hc ⊢
    have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
    push_cast at hc ⊢
    rw [show (m : ℝ) + 2 - 1 = m + 1 by ring, inv_div, div_mul_div_comm, mul_div_assoc',
      div_eq_div_iff h1 (by positivity)]
    linear_combination 2 * hc
  rw [totalMergerRate, sum_congr rfl hterm, ← mul_sum, sum_inv_choose_two hb]
  have : (b : ℝ) ≠ 0 := by positivity
  field_simp

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
