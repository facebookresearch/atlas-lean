/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Order.Interval.Set.Basic

import Mathlib.Data.Nat.Init
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Life-table demography: balance, survival, and direct standardization

Cohort accounting with deaths and net migration/error, closed-cohort
survival as a product of one-step survival probabilities, and direct
age-standardization with the rate/composition decomposition of crude-rate
differences. Counts are real sequences indexed by `ℕ`. Death probabilities
and central rates are only defined on positive risk sets and exposures.
Categories form a finite type; sizes and rates are real functions; totals
may be zero, in which case shares and crude rates take the junk value `0`.
The algebraic identities (share-weighted sums, the `centerMass` bridge,
standardization, and both decompositions) hold for all real sizes, junk
values included, and carry no hypotheses. Demographic corollaries (shares in
`[0, 1]`, crude and standardized rates within the range of the category
rates) assume `IsValidPopulation`: nonnegative sizes with a positive total,
which excludes signed "counts" as well as empty and all-zero populations.
`crudeRate` is defined as `Finset.univ.centerMass` and
`directlyStandardizedRate` as the crude rate with the standard's composition,
so both bridges are `rfl`; `crudeRate_eq_sum_mul_div` recovers the Das Gupta
formula. `crudeRate` parallels `MendelianRandomization.weightedMean`, which is
not imported to keep `Demography` independent.

## Main definitions

- `deathProbability`: death probability on `[x, x + 1)` over `l x`.
- `centralDeathRate`: deaths over positive exposure.
- `populationShare`: share of category `i` in the total.
- `crudeRate`: crude rate, the size-weighted mean `Finset.univ.centerMass`
  of the category rates.
- `directlyStandardizedRate`: crude rate under the standard's composition.
- `IsValidPopulation`: nonnegative category sizes with a positive total.

## Main results

- `cohort_balance`: open population balance over `T` years.
- `closed_cohort_balance`: closed population balance over `T` years.
- `extinct_cohort`: initial size equals total deaths when extinct.
- `mul_deathProbability`: risk set times probability recovers deaths.
- `deathProbability_mem_Icc`: death probability lies in `[0, 1]`.
- `survivors_succ_eq_mul`: one-step survival as multiplication.
- `survivors_eq_mul_prod`: survivors as initial size times product.
- `survivors_eq_zero_of_le`: extinct closed cohorts stay extinct.
- `crudeRate_eq_sum_mul_div`: crude rate as total events over total size.
- `crudeRate_eq_sum_populationShare_mul`: crude rate as share-weighted sum.
- `crudeRate_eq_centerMass`: crude rate is `Finset.univ.centerMass`
  (by definition).
- `directlyStandardizedRate_eq_crudeRate`: standardized rate is the crude
  rate with the standard's composition.
- `crudeRate_centralDeathRate`: crude death rate as total deaths over total
  exposure.
- `crudeRate_sub_crudeRate`: rate/composition decomposition of crude-rate
  differences.
- `crudeRate_sub_crudeRate_of_same_rates`: equal rates leave only the
  composition effect, as a `directlyStandardizedRate` difference.
- `sum_populationShare`: shares sum to `1` when the total is nonzero.
- `populationShare_mem_Icc`, `crudeRate_mem_Icc`,
  `directlyStandardizedRate_mem_Icc`: for a valid population, shares lie in
  `[0, 1]` and crude and standardized rates lie in any interval containing
  every category rate.

## Not covered

- Life expectancy
- `ax` / person-years formulas
- Lexis-triangle splitting
- Period-versus-cohort tables
- Leslie matrices
- More than two populations
- More than one compositional factor
- Indirect standardization
- Life expectancy decomposition
- Standard errors

## References

- J. R. Wilmoth, K. Andreev, D. Jdanov, D. A. Glei, T. Riffe et al.,
  Methods Protocol for the Human Mortality Database, Version 6 (2025),
  Section 4, eqs. (9)-(11); Section 6, eq. (49); Section 7.1,
  eqs. (78)-(80); Section 7.2, eq. (84).
- `cohort_balance` follows (10)-(11); `closed_cohort_balance` is the case
  with no migration or error; `extinct_cohort` follows (9);
  `mul_deathProbability` follows (80); `survivors_succ_eq_mul` follows (78);
  `survivors_eq_mul_prod` follows (79).
- P. Das Gupta, Standardization and Decomposition of Rates: A User's Manual,
  U.S. Bureau of the Census, Current Population Reports P23-186 (1993):
  `populationShare`, `crudeRate_eq_sum_mul_div`, and
  `crudeRate_eq_sum_populationShare_mul` follow (5.1)-(5.2);
  `directlyStandardizedRate` and `directlyStandardizedRate_eq_crudeRate`
  follow Chapter 1; `crudeRate_sub_crudeRate` follows (5.3)-(5.4) with the
  averaged standard of E. M. Kitagawa (1955).
-/

@[expose] public section

namespace MathlibExt.Biology.Demography.LifeTable

/-- Death probability on `[x, x + 1)` over the positive risk set `l x`, HMD (80), (84). -/
noncomputable def deathProbability (l d : ℕ → ℝ) (x : ℕ) (_hx : 0 < l x) : ℝ :=
  d x / l x

/-- Central death rate, deaths over positive exposure, HMD (49). -/
noncomputable def centralDeathRate (D E : ℝ) (_hE : 0 < E) : ℝ :=
  D / E

/-- Cohort balance over `T` years with deaths and net migration, HMD (10)-(11). -/
theorem cohort_balance (P D M : ℕ → ℝ) (hstep : ∀ t, P (t + 1) = P t - D t + M t) (T : ℕ) :
    P T = P 0 - ∑ t ∈ Finset.range T, D t + ∑ t ∈ Finset.range T, M t := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [hstep n, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- Closed cohort balance with no migration or error. -/
theorem closed_cohort_balance (P D : ℕ → ℝ) (hstep : ∀ t, P (t + 1) = P t - D t) (T : ℕ) :
    P T = P 0 - ∑ t ∈ Finset.range T, D t := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [hstep n, ih, Finset.sum_range_succ]
    ring

/-- Extinct cohort initial size equals total deaths, HMD (9). -/
theorem extinct_cohort (P D : ℕ → ℝ) (hstep : ∀ t, P (t + 1) = P t - D t) {T : ℕ}
    (hT : P T = 0) :
    P 0 = ∑ t ∈ Finset.range T, D t := by
  have h := closed_cohort_balance P D hstep T
  rw [hT] at h
  linarith

/-- Risk set times death probability recovers deaths, HMD (80). -/
theorem mul_deathProbability (l d : ℕ → ℝ) (x : ℕ) (hx : 0 < l x) :
    l x * deathProbability l d x hx = d x := by
  unfold deathProbability
  have hne : l x ≠ 0 := hx.ne'
  rw [mul_comm, div_mul_cancel₀ _ hne]

/-- Death probability lies in `[0, 1]` when `0 ≤ d x ≤ l x`. -/
theorem deathProbability_mem_Icc (l d : ℕ → ℝ) (x : ℕ) (hx : 0 < l x)
    (hd0 : 0 ≤ d x) (hdle : d x ≤ l x) :
    deathProbability l d x hx ∈ Set.Icc (0 : ℝ) 1 := by
  unfold deathProbability
  rw [Set.mem_Icc]
  exact ⟨div_nonneg hd0 (le_of_lt hx), (div_le_one hx).mpr hdle⟩

/-- One-step survival as multiplication by `1 - q`, HMD (78). -/
theorem survivors_succ_eq_mul (l d : ℕ → ℝ) (hstep : ∀ x, l (x + 1) = l x - d x) (x : ℕ)
    (hx : 0 < l x) :
    l (x + 1) = l x * (1 - deathProbability l d x hx) := by
  have h := mul_deathProbability l d x hx
  rw [hstep x, mul_sub, mul_one, h]

/-- Survivors as initial size times survival product, HMD (79). -/
theorem survivors_eq_mul_prod (l d : ℕ → ℝ) (hstep : ∀ x, l (x + 1) = l x - d x) (x : ℕ)
    (hpos : ∀ k : Fin x, 0 < l k) :
    l x = l 0 * ∏ k : Fin x, (1 - deathProbability l d k (hpos k)) := by
  have aux : ∀ (y : ℕ) (hp : ∀ k : Fin y, 0 < l k),
    l y = l 0 * ∏ k : Fin y, (1 - deathProbability l d k (hp k)) := by
    intro y
    induction y with
    | zero =>
      intro hp
      simp
    | succ n ih =>
      intro hp
      have hx_n : 0 < l n := by
        have hlast := hp (Fin.last n)
        simpa [Fin.val_last] using hlast
      have hp_n : ∀ k : Fin n, 0 < l k := by
        intro k
        have hcast := hp k.castSucc
        simpa [Fin.val_castSucc] using hcast
      have ih' := ih hp_n
      have hsucc := survivors_succ_eq_mul l d hstep n hx_n
      have hprod : (∏ k : Fin (n + 1), (1 - deathProbability l d k (hp k))) =
        (∏ k : Fin n, (1 - deathProbability l d k.castSucc (hp k.castSucc))) *
        (1 - deathProbability l d (Fin.last n) (hp (Fin.last n))) :=
        Fin.prod_univ_castSucc _
      have hcast_eq : (∏ k : Fin n, (1 - deathProbability l d k.castSucc (hp k.castSucc))) =
        ∏ k : Fin n, (1 - deathProbability l d k (hp_n k)) := by
        apply Finset.prod_congr rfl
        intro k _
        simp only [deathProbability, Fin.val_castSucc]
      have hlast_eq : (1 - deathProbability l d (Fin.last n) (hp (Fin.last n))) =
        (1 - deathProbability l d n hx_n) := by
        simp only [deathProbability, Fin.val_last]
      rw [hsucc, ih', hprod, hcast_eq, hlast_eq]
      ring
  exact aux x hpos

/-- Zero survivors: a closed cohort with deaths in `[0, l x]` stays extinct. -/
theorem survivors_eq_zero_of_le (l d : ℕ → ℝ) (hstep : ∀ x, l (x + 1) = l x - d x)
    (hd : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ l x) {k x : ℕ} (hk : l k = 0) (hkx : k ≤ x) :
    l x = 0 := by
  induction x, hkx using Nat.le_induction with
  | base => exact hk
  | succ n hle_n ih =>
    have hdn : 0 ≤ d n := hd n
    have hlen : d n ≤ l n := hle n
    rw [ih] at hlen
    have hdn0 : d n = 0 := le_antisymm hlen hdn
    rw [hstep n, ih, hdn0, sub_zero]

/-- Share of category `i`, Das Gupta (5.2); junk value `0` when the total
  is `0`. Demographic corollaries assume `IsValidPopulation`. -/
noncomputable def populationShare {ι : Type*} [Fintype ι] (N : ι → ℝ) (i : ι) : ℝ :=
  N i / ∑ j, N j

/-- Crude rate from sizes `N` and rates `T`: the size-weighted mean
  `Finset.univ.centerMass N T`, which is Das Gupta (5.1)
  (`crudeRate_eq_sum_mul_div`); junk value `0` when the total is `0`.
  Demographic corollaries assume `IsValidPopulation`. -/
noncomputable def crudeRate {ι : Type*} [Fintype ι] (N T : ι → ℝ) : ℝ :=
  Finset.univ.centerMass N T

/-- Directly standardized rate of `T` under standard `S`, Das Gupta Ch. 1: the
  crude rate with the standard's composition; junk `0` when the standard's
  total is `0`. Demographic corollaries assume `IsValidPopulation S`. -/
noncomputable def directlyStandardizedRate {ι : Type*} [Fintype ι] (S T : ι → ℝ) : ℝ :=
  crudeRate S T

/-- A valid population: nonnegative category sizes with a positive total. The
  demographic corollaries assume it; the algebraic identities need no
  hypothesis on the sizes. -/
structure IsValidPopulation {ι : Type*} [Fintype ι] (N : ι → ℝ) : Prop where
  /-- Every category size is nonnegative. -/
  nonneg : ∀ i, 0 ≤ N i
  /-- The total size is positive. -/
  sum_pos : 0 < ∑ i, N i

/-- Crude rate as total events over total size, Das Gupta (5.1); holds for all
  real sizes, including zero total. -/
theorem crudeRate_eq_sum_mul_div {ι : Type*} [Fintype ι] (N T : ι → ℝ) :
    crudeRate N T = (∑ i, T i * N i) / ∑ i, N i := by
  unfold crudeRate Finset.centerMass
  rw [div_eq_inv_mul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, mul_comm]

/-- Crude rate as a share-weighted sum, Das Gupta (5.1)-(5.2); holds for all
  real sizes, including zero total. -/
theorem crudeRate_eq_sum_populationShare_mul {ι : Type*} [Fintype ι] (N T : ι → ℝ) :
    crudeRate N T = ∑ i, populationShare N i * T i := by
  rw [crudeRate_eq_sum_mul_div]
  unfold populationShare
  have h : ∀ i, N i / (∑ j, N j) * T i = (T i * N i) / ∑ j, N j := fun i => by
    ring
  simp only [h, Finset.sum_div]

/-- Crude rate is `Finset.univ.centerMass`, by definition. -/
theorem crudeRate_eq_centerMass {ι : Type*} [Fintype ι] (N T : ι → ℝ) :
    crudeRate N T = Finset.univ.centerMass N T :=
  rfl

/-- Standardized rate is the crude rate with the standard's composition, by
  definition. -/
theorem directlyStandardizedRate_eq_crudeRate {ι : Type*} [Fintype ι] (S T : ι → ℝ) :
    directlyStandardizedRate S T = crudeRate S T :=
  rfl

/-- Crude rate of central death rates is total deaths over total exposure; the
  positive exposures are needed only to define the central rates. -/
theorem crudeRate_centralDeathRate {ι : Type*} [Fintype ι] (D N : ι → ℝ)
    (hN : ∀ i, 0 < N i) :
    crudeRate N (fun i => centralDeathRate (D i) (N i) (hN i)) = (∑ i, D i) / ∑ i, N i := by
  rw [crudeRate_eq_sum_mul_div]
  unfold centralDeathRate
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact div_mul_cancel₀ _ (ne_of_gt (hN i))

/-- Rate/composition decomposition of crude-rate differences, Das Gupta
  (5.3)-(5.4) with the Kitagawa (1955) averaged standard. The first bracket
  is the rate effect (5.3) and the second is the composition effect (5.4).
  Holds for all real sizes, including zero totals. -/
theorem crudeRate_sub_crudeRate {ι : Type*} [Fintype ι] (N n T t : ι → ℝ) :
    crudeRate n t - crudeRate N T =
      (∑ i, (populationShare n i + populationShare N i) / 2 * t i -
        ∑ i, (populationShare n i + populationShare N i) / 2 * T i) +
      (∑ i, (t i + T i) / 2 * populationShare n i -
        ∑ i, (t i + T i) / 2 * populationShare N i) := by
  rw [crudeRate_eq_sum_populationShare_mul n t, crudeRate_eq_sum_populationShare_mul N T]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Equal rates leave only the composition effect, as a `directlyStandardizedRate`
  difference; holds for all real sizes, including zero totals. -/
theorem crudeRate_sub_crudeRate_of_same_rates {ι : Type*} [Fintype ι] (N n T : ι → ℝ) :
    crudeRate n T - crudeRate N T = ∑ i, T i * (populationShare n i - populationShare N i) ∧
      ∑ i, T i * (populationShare n i - populationShare N i) =
        directlyStandardizedRate n T - directlyStandardizedRate N T := by
  have hsum : crudeRate n T - crudeRate N T =
      ∑ i, T i * (populationShare n i - populationShare N i) := by
    rw [crudeRate_eq_sum_populationShare_mul n T, crudeRate_eq_sum_populationShare_mul N T]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ⟨hsum, hsum.symm⟩

/-- Shares sum to `1` when the total is nonzero. -/
theorem sum_populationShare {ι : Type*} [Fintype ι] {N : ι → ℝ} (hN : ∑ i, N i ≠ 0) :
    ∑ i, populationShare N i = 1 := by
  unfold populationShare
  rw [← Finset.sum_div, div_self hN]

/-- Shares of a valid population lie in `[0, 1]`. -/
theorem populationShare_mem_Icc {ι : Type*} [Fintype ι] {N : ι → ℝ}
    (hN : IsValidPopulation N) (i : ι) : populationShare N i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold populationShare
  refine ⟨div_nonneg (hN.nonneg i) hN.sum_pos.le, (div_le_one hN.sum_pos).mpr ?_⟩
  exact Finset.single_le_sum (fun j _ => hN.nonneg j) (Finset.mem_univ i)

/-- The crude rate of a valid population lies in any interval `[a, b]` that
  contains every category rate. -/
theorem crudeRate_mem_Icc {ι : Type*} [Fintype ι] {N T : ι → ℝ} (hN : IsValidPopulation N)
    {a b : ℝ} (hT : ∀ i, T i ∈ Set.Icc a b) : crudeRate N T ∈ Set.Icc a b := by
  rw [crudeRate_eq_sum_mul_div]
  rw [Set.mem_Icc, le_div_iff₀ hN.sum_pos, div_le_iff₀ hN.sum_pos, Finset.mul_sum,
    Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hT i).1 (hN.nonneg i),
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hT i).2 (hN.nonneg i)⟩

/-- The rate standardized to a valid standard lies in any interval `[a, b]`
  that contains every category rate. -/
theorem directlyStandardizedRate_mem_Icc {ι : Type*} [Fintype ι] {S T : ι → ℝ}
    (hS : IsValidPopulation S) {a b : ℝ} (hT : ∀ i, T i ∈ Set.Icc a b) :
    directlyStandardizedRate S T ∈ Set.Icc a b := by
  rw [directlyStandardizedRate_eq_crudeRate]
  exact crudeRate_mem_Icc hS hT

end MathlibExt.Biology.Demography.LifeTable
