/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Integration
public import MathlibExt.Probability.Statistics.TwoGroupsTesting

/-!
# Adaptive FDR control: the Storey-BH procedure

Benjamini–Hochberg (BH) at level `q` controls the false discovery rate at `q |H0| / m`, which is
conservative when the proportion `π₀ = |H0| / m` of true nulls is small. Storey's adaptive
procedure estimates `π₀` from the p-values,
`π̂₀(lam) = (#{j : p j > lam} + 1) / ((1 - lam) m)` (`storeyPi0Plus1`), and runs BH at the larger
level `q / π̂₀(lam)`, rejecting only p-values `≤ lam` (`storeyThreshold`, `storeyBHIndex`,
`storeyBHRejections`).

Storey, Taylor and Siegmund (2004, Theorem 3) proved that this procedure controls the FDR at `q`
(not `q π₀`) when the null p-values are independent and valid. The proof here is the
leave-one-out argument:

1. *Interaction of the adaptive threshold with `p i`* (`storeyBH_leave_one_out`): on
   `{i rejected}` we have `p i ≤ lam`, so `π̂₀` and the number of rejections coincide with those
   computed from the vector with `p i := 0`, which depend only on the other p-values. Independence
   and validity of `p i` then give `E[1{i ∈ R} / |R|] ≤ (q / m) E[1 / π̂₀⁽ⁱ⁾]`.
2. *Estimator property* (`sum_integral_inv_storeyPi0Plus1_update_le`):
   `∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m`.

Storey's (2002) estimator without the `+ 1`, its conservativeness in expectation
`E[π̂₀] ≥ |H0| / m`, and the q-value are already on main as `TwoGroupsTesting.storeyPi0`,
`TwoGroupsTesting.le_integral_storeyPi0` and `TwoGroupsTesting.qValue`. The FDR theorem needs the
`+ 1` form of Storey, Taylor and Siegmund (2004), so it is a separate definition, `storeyPi0Plus1`,
related to main's by `storeyPi0Plus1_eq_storeyPi0_add` and `storeyPi0_le_storeyPi0Plus1`.
Conservativeness in expectation is not used and does not suffice: the test file has an exactly
unbiased estimator of `π₀` whose plug-in BH procedure has FDR `1/3` at `q = 1/4`.

## Conditions, stated explicitly

* **Validity**: every true-null p-value is super-uniform (`IsValidPValue`).
* **Independence**: every true-null `p i` is independent of the vector `(p j)_{j ≠ i}` of all other
  p-values. Mutual independence implies this (`indepFun_rest_of_iIndepFun`). Nothing is assumed
  about the false-null p-values among themselves. PRDS is *not* enough for this proof, and the
  theorem is not claimed under PRDS.
* **Fixed tuning parameter**: `lam ∈ [0, 1)` is a constant. The test file shows that picking
  `lam` after seeing the p-values breaks FDR control: on a two-null model with valid,
  independent p-values and `q = 1/4`, every fixed `lam` gives `FDR ≤ 1/4` while choosing the
  `lam ∈ {1/9, 1/3}` with more rejections gives `FDR = 7/27`.
* **Cap at `lam`** and the **`+ 1`** in `π̂₀`: both are part of the procedure and used in the proof.

## Main results

* `storeyBH_leave_one_out`: the leave-one-out property of Storey-BH.
* `sum_integral_inv_storeyPi0Plus1_update_le`: `∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m`.
* `integral_falseDiscoveryProportion_storeyBHRejections_le`: `E[FDP] ≤ q`.
* `integral_falseDiscoveryProportion_storeyBHRejections_le_of_iIndepFun`: the same under
  mutual independence.
* `storeyPi0Plus1_eq_storeyPi0_add`, `storeyPi0_le_storeyPi0Plus1`: relation to
  `TwoGroupsTesting.storeyPi0`.

## Not covered

FDR control of the Storey q-value procedure (`TwoGroupsTesting.qValue` applied to a pFDR estimate)
or of Storey-BH with a data-dependent `lam` (or a `lam`-grid chosen by bootstrap), FDR control
under PRDS or arbitrary dependence (where Storey-BH can fail), and the asymptotic results of Storey
et al. (2004, §4) are not formalized.

## Follow-up

`numBelow_update_le'`, `numBelow_update_eq'`, `fdp_eq_sum` and `valid_measureReal_le` re-prove
private lemmas of `MultipleTesting.BenjaminiHochberg`, and the generic step-up leave-one-out
(`suIdx`, `su_leave_one_out`) could replace `bhIndex`'s copy. Moving them to
`MultipleTesting.Basic` as public lemmas is left to a follow-up that edits that file.

## References

* J. D. Storey, *A direct approach to false discovery rates*, J. R. Statist. Soc. B 64 (2002),
  479–498.
* J. D. Storey, J. E. Taylor and D. Siegmund, *Strong control, conservative point estimation and
  simultaneous conservative consistency of false discovery rates: a unified approach*,
  J. R. Statist. Soc. B 66 (2004), 187–205, Theorem 3.
* G. Blanchard and É. Roquain, *Adaptive false discovery rate control under independence and
  dependence*, J. Mach. Learn. Res. 10 (2009), 2837–2871.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-- **Storey's estimator of the proportion of true nulls** with tuning parameter `lam`, in the
finite-sample form used by Storey, Taylor and Siegmund (2004, Theorem 3):
`π̂₀(lam) = (#{j : p j > lam} + 1) / ((1 - lam) m)`. The `+ 1` keeps `π̂₀ > 0` and is used in the
FDR proof (`sum_integral_inv_storeyPi0Plus1_update_le`). -/
noncomputable def storeyPi0Plus1 (lam : ℝ) (p : Fin m → ℝ) : ℝ :=
  (((Finset.univ.filter fun j => lam < p j).card : ℝ) + 1) / ((1 - lam) * m)

/-- The thresholds of the **Storey-BH** step-up procedure: BH at the adaptive level
`q / π̂₀(lam)`, capped at `lam`, so the `k`-th threshold is `min lam (q k / (m π̂₀(lam)))`. Only
p-values `≤ lam` can be rejected (Storey, Taylor and Siegmund 2004, Theorem 3). -/
noncomputable def storeyThreshold (q lam : ℝ) (p : Fin m → ℝ) (k : ℕ) : ℝ :=
  min lam (q / storeyPi0Plus1 lam p * k / m)

/-- The Storey-BH step-up index: the largest `k ∈ {0, …, m}` such that at least `k` p-values are
at most `storeyThreshold q lam p k` (`k = 0` always qualifies). -/
noncomputable def storeyBHIndex (q lam : ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ =>
    k ≤ numBelow p (storeyThreshold q lam p k)).max' ⟨0, by simp⟩

/-- The hypotheses rejected by the **Storey-BH** procedure at level `q` with tuning parameter
`lam`: those whose p-value is at most `storeyThreshold q lam p (storeyBHIndex q lam p)`. -/
noncomputable def storeyBHRejections (q lam : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ storeyThreshold q lam p (storeyBHIndex q lam p)

/-! ### Step-up procedures with a fixed nondecreasing threshold sequence -/

/-- Step-up index for an arbitrary threshold sequence `c`. -/
private noncomputable def suIdx (c : ℕ → ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ => k ≤ numBelow p (c k)).max' ⟨0, by simp⟩

private theorem suIdx_mem (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p ∈ (Finset.range (m + 1)).filter fun k : ℕ => k ≤ numBelow p (c k) :=
  Finset.max'_mem _ _

private theorem suIdx_le (c : ℕ → ℝ) (p : Fin m → ℝ) : suIdx c p ≤ m := by
  have h := suIdx_mem c p
  simp only [Finset.mem_filter, Finset.mem_range] at h
  omega

private theorem suIdx_le_numBelow (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p ≤ numBelow p (c (suIdx c p)) := by
  have h := suIdx_mem c p
  simp only [Finset.mem_filter] at h
  exact h.2

private theorem le_suIdx {c : ℕ → ℝ} {p : Fin m → ℝ} {k : ℕ} (hk : k ≤ m)
    (h : k ≤ numBelow p (c k)) : k ≤ suIdx c p :=
  Finset.le_max' _ k (by simpa [Nat.lt_succ_iff] using ⟨hk, h⟩)

private theorem numBelow_suIdx {c : ℕ → ℝ} (hc : Monotone c) (p : Fin m → ℝ) :
    numBelow p (c (suIdx c p)) = suIdx c p := by
  refine le_antisymm ?_ (suIdx_le_numBelow c p)
  by_contra! hlt
  have hle : numBelow p (c (suIdx c p)) ≤ suIdx c p :=
    le_suIdx (numBelow_le p _) (numBelow_mono p (hc hlt.le))
  omega

private theorem numBelow_update_le' (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) : numBelow p t ≤ numBelow (Function.update p i 0) t := by
  classical
  apply Finset.card_le_card
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases hji : j = i
  · simpa [hji] using ht
  · simpa [Function.update_of_ne hji] using (Finset.mem_filter.mp hj).2

private theorem numBelow_update_eq' (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) (hpi : p i ≤ t) : numBelow (Function.update p i 0) t = numBelow p t := by
  classical
  unfold numBelow
  congr 1
  ext j
  by_cases hji : j = i
  · simp [hji, ht, hpi]
  · simp [Function.update_of_ne hji]

private theorem suIdx_le_update {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) : suIdx c p ≤ suIdx c (Function.update p i 0) :=
  le_suIdx (suIdx_le c p) ((suIdx_le_numBelow c p).trans (numBelow_update_le' p i (hc0 _)))

private theorem one_le_suIdx_update {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) : 1 ≤ suIdx c (Function.update p i 0) := by
  apply le_suIdx (by have := i.isLt; omega)
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hc0 1⟩⟩

private theorem suIdx_update_eq {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) (hpi : p i ≤ c (suIdx c (Function.update p i 0))) :
    suIdx c p = suIdx c (Function.update p i 0) := by
  apply le_antisymm (suIdx_le_update hc0 p i)
  apply le_suIdx (suIdx_le c _)
  rw [← numBelow_update_eq' p i (hc0 _) hpi]
  exact suIdx_le_numBelow c _

/-- Leave-one-out property of step-up procedures (with a threshold sequence that does not depend
on the data): `i` is rejected and `k` hypotheses are rejected iff `p i ≤ c k` and the procedure
applied with `p i` replaced by `0` rejects `k` hypotheses. -/
private theorem su_leave_one_out {c : ℕ → ℝ} (hc : Monotone c) (hc0 : ∀ k, 0 ≤ c k)
    (p : Fin m → ℝ) (i : Fin m) (k : ℕ) :
    (p i ≤ c (suIdx c p) ∧ suIdx c p = k) ↔
      (p i ≤ c k ∧ suIdx c (Function.update p i 0) = k) := by
  constructor
  · rintro ⟨hpi, hk⟩
    have heq := suIdx_update_eq hc0 p i (hpi.trans (hc (suIdx_le_update hc0 p i)))
    exact ⟨hk ▸ hpi, heq.symm.trans hk⟩
  · rintro ⟨hpi, hk⟩
    have heq := suIdx_update_eq hc0 p i (by rwa [hk])
    exact ⟨by rw [heq, hk]; exact hpi, heq.trans hk⟩

/-! ### Basic properties of Storey's estimator and the Storey-BH procedure -/

/-- Storey's estimator is nonnegative for `lam ≤ 1`. -/
theorem storeyPi0Plus1_nonneg {lam : ℝ} (hlam : lam ≤ 1) (p : Fin m → ℝ) :
    0 ≤ storeyPi0Plus1 lam p := by
  unfold storeyPi0Plus1
  have : 0 ≤ 1 - lam := by linarith
  positivity

/-- Replacing a p-value `p i ≤ lam` by `0` does not change Storey's estimator when `0 ≤ lam`:
only p-values above `lam` are counted. -/
theorem storeyPi0Plus1_update_zero {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin m → ℝ) (i : Fin m)
    (hpi : p i ≤ lam) : storeyPi0Plus1 lam (Function.update p i 0) = storeyPi0Plus1 lam p := by
  classical
  unfold storeyPi0Plus1
  congr 4
  ext j
  by_cases hji : j = i
  · subst hji
    simp [not_lt.mpr hlam, not_lt.mpr hpi]
  · simp [Function.update_of_ne hji]

/-- With `m > 0`, the Storey-BH thresholds are
`min lam (q (1 - lam) k / (#{j : p j > lam} + 1))`. -/
theorem storeyThreshold_eq (hm : m ≠ 0) (q lam : ℝ) (p : Fin m → ℝ) (k : ℕ) :
    storeyThreshold q lam p k =
      min lam (q * (1 - lam) * k / ((Finset.univ.filter fun j => lam < p j).card + 1)) := by
  unfold storeyThreshold storeyPi0Plus1
  congr 1
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [div_div_eq_mul_div]
  field_simp

/-- The Storey-BH thresholds never exceed `lam`. -/
theorem storeyThreshold_le (q lam : ℝ) (p : Fin m → ℝ) (k : ℕ) :
    storeyThreshold q lam p k ≤ lam :=
  min_le_left _ _

/-- The Storey-BH thresholds are nonnegative for `0 ≤ q` and `0 ≤ lam ≤ 1`. -/
theorem storeyThreshold_nonneg {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (p : Fin m → ℝ) (k : ℕ) : 0 ≤ storeyThreshold q lam p k := by
  have := storeyPi0Plus1_nonneg hlam1 p
  exact le_min hlam0 (by positivity)

/-- The Storey-BH thresholds are nondecreasing in `k` for `0 ≤ q` and `lam ≤ 1`. -/
theorem storeyThreshold_mono {q lam : ℝ} (hq : 0 ≤ q) (hlam1 : lam ≤ 1) (p : Fin m → ℝ) :
    Monotone (storeyThreshold q lam p) := by
  intro k l hkl
  have := storeyPi0Plus1_nonneg hlam1 p
  refine min_le_min le_rfl ?_
  have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
  gcongr

/-- Replacing `p i ≤ lam` by `0` does not change the Storey-BH thresholds when `0 ≤ lam`. -/
theorem storeyThreshold_update_zero {q lam : ℝ} (hlam : 0 ≤ lam) (p : Fin m → ℝ) (i : Fin m)
    (hpi : p i ≤ lam) :
    storeyThreshold q lam (Function.update p i 0) = storeyThreshold q lam p := by
  funext k
  simp only [storeyThreshold, storeyPi0Plus1_update_zero hlam p i hpi]

private theorem storeyBHIndex_eq_suIdx (q lam : ℝ) (p : Fin m → ℝ) :
    storeyBHIndex q lam p = suIdx (storeyThreshold q lam p) p := rfl

/-- The Storey-BH step-up index is at most `m`. -/
theorem storeyBHIndex_le (q lam : ℝ) (p : Fin m → ℝ) : storeyBHIndex q lam p ≤ m :=
  suIdx_le _ p

/-- At the Storey-BH index `k`, at least `k` p-values are at most the `k`-th threshold. -/
theorem storeyBHIndex_le_numBelow (q lam : ℝ) (p : Fin m → ℝ) :
    storeyBHIndex q lam p ≤ numBelow p (storeyThreshold q lam p (storeyBHIndex q lam p)) :=
  suIdx_le_numBelow _ p

/-- The Storey-BH index is the largest qualifying `k ≤ m`. -/
theorem le_storeyBHIndex {q lam : ℝ} {p : Fin m → ℝ} {k : ℕ} (hk : k ≤ m)
    (h : k ≤ numBelow p (storeyThreshold q lam p k)) : k ≤ storeyBHIndex q lam p :=
  le_suIdx hk h

/-- Storey-BH with `0 ≤ q` and `lam ≤ 1` rejects exactly `storeyBHIndex q lam p` hypotheses. -/
theorem card_storeyBHRejections {q lam : ℝ} (hq : 0 ≤ q) (hlam1 : lam ≤ 1) (p : Fin m → ℝ) :
    (storeyBHRejections q lam p).card = storeyBHIndex q lam p :=
  numBelow_suIdx (storeyThreshold_mono hq hlam1 p) p

/-- Membership in the Storey-BH rejection set. -/
theorem mem_storeyBHRejections {q lam : ℝ} {p : Fin m → ℝ} {i : Fin m} :
    i ∈ storeyBHRejections q lam p ↔ p i ≤ storeyThreshold q lam p (storeyBHIndex q lam p) := by
  simp [storeyBHRejections]

/-- Storey-BH (with `0 ≤ q`, `lam ≤ 1`) rejects something iff some `k ∈ [1, m]` has at least `k`
p-values below the `k`-th threshold. -/
theorem storeyBHRejections_nonempty_iff {q lam : ℝ} (hq : 0 ≤ q) (hlam1 : lam ≤ 1)
    (p : Fin m → ℝ) : (storeyBHRejections q lam p).Nonempty ↔
      ∃ k ∈ Finset.Icc 1 m, k ≤ numBelow p (storeyThreshold q lam p k) := by
  rw [← Finset.card_pos, card_storeyBHRejections hq hlam1]
  constructor
  · intro h
    exact ⟨_, Finset.mem_Icc.mpr ⟨h, storeyBHIndex_le q lam p⟩, storeyBHIndex_le_numBelow q lam p⟩
  · rintro ⟨k, hk, hkn⟩
    exact lt_of_lt_of_le (Finset.mem_Icc.mp hk).1 (le_storeyBHIndex (Finset.mem_Icc.mp hk).2 hkn)

/-- Storey-BH only rejects p-values that are at most `lam`. -/
theorem le_of_mem_storeyBHRejections {q lam : ℝ} {p : Fin m → ℝ} {i : Fin m}
    (hi : i ∈ storeyBHRejections q lam p) : p i ≤ lam :=
  (mem_storeyBHRejections.mp hi).trans (storeyThreshold_le _ _ _ _)

/-- **Leave-one-out property of Storey-BH.** For `0 ≤ q` and `0 ≤ lam ≤ 1`, hypothesis `i` is
rejected and exactly `k` hypotheses are rejected iff `p i` is at most the `k`-th threshold of the
vector `p⁰` with `p i` replaced by `0`, and Storey-BH rejects exactly `k` hypotheses of `p⁰`. The
right side depends on `p i` only through the event `p i ≤ ·`, because on rejection `p i ≤ lam`, so
`p i` does not enter Storey's estimator. This is the step where the cap at `lam` is used. -/
theorem storeyBH_leave_one_out {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (p : Fin m → ℝ) (i : Fin m) (k : ℕ) :
    (i ∈ storeyBHRejections q lam p ∧ (storeyBHRejections q lam p).card = k) ↔
      (p i ≤ storeyThreshold q lam (Function.update p i 0) k ∧
        (storeyBHRejections q lam (Function.update p i 0)).card = k) := by
  rw [card_storeyBHRejections hq hlam1, card_storeyBHRejections hq hlam1,
    mem_storeyBHRejections, storeyBHIndex_eq_suIdx, storeyBHIndex_eq_suIdx]
  have hmono := storeyThreshold_mono hq hlam1 (Function.update p i 0)
  have h0 := storeyThreshold_nonneg hq hlam0 hlam1 (Function.update p i 0)
  constructor
  · rintro ⟨hpi, hk⟩
    have hc := storeyThreshold_update_zero (q := q) hlam0 p i
      (hpi.trans (storeyThreshold_le _ _ _ _))
    rw [← hc] at hpi hk
    exact (su_leave_one_out hmono h0 p i k).mp ⟨hpi, hk⟩
  · rintro ⟨hpi, hk⟩
    have hc := storeyThreshold_update_zero (q := q) hlam0 p i
      (hpi.trans (storeyThreshold_le _ _ _ _))
    rw [← hc]
    exact (su_leave_one_out hmono h0 p i k).mpr ⟨hpi, hk⟩

/-! ### Measurability -/

private theorem suIdx_eq_sup (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p = (Finset.range (m + 1)).sup
      (fun k => if k ≤ numBelow p (c k) then k else 0) := by
  classical
  apply le_antisymm
  · have h := Finset.le_sup (f := fun (k : ℕ) => if k ≤ numBelow p (c k) then k else 0)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (suIdx_le c p)))
    simpa [suIdx_le_numBelow c p] using h
  · apply Finset.sup_le
    intro k hk
    split_ifs with h
    · exact le_suIdx (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h
    · exact Nat.zero_le _

private theorem measurable_numBelow_comp {Y : Type*} [MeasurableSpace Y] (x : Y → Fin m → ℝ)
    (hx : ∀ j, Measurable fun y => x y j) {t : Y → ℝ} (ht : Measurable t) :
    Measurable fun y => numBelow (x y) (t y) := by
  classical
  simp only [numBelow, Finset.card_filter]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_le (hx j) ht) measurable_const measurable_const

private theorem measurable_numAbove_comp {Y : Type*} [MeasurableSpace Y] (x : Y → Fin m → ℝ)
    (hx : ∀ j, Measurable fun y => x y j) (lam : ℝ) :
    Measurable fun y => (Finset.univ.filter fun j => lam < x y j).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_lt measurable_const (hx j)) measurable_const measurable_const

private theorem measurable_suIdx_comp {Y : Type*} [MeasurableSpace Y] (c : Y → ℕ → ℝ)
    (x : Y → Fin m → ℝ) (hc : ∀ k, Measurable fun y => c y k)
    (hx : ∀ j, Measurable fun y => x y j) : Measurable fun y => suIdx (c y) (x y) := by
  classical
  simp_rw [suIdx_eq_sup]
  have h : ∀ s : Finset ℕ, Measurable (fun y => s.sup
      (fun k => if k ≤ numBelow (x y) (c y k) then k else 0)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.sup_insert]
      exact (Measurable.ite (measurableSet_le measurable_const
        (measurable_numBelow_comp x hx (hc k))) measurable_const measurable_const).max ih
  exact h _

private theorem measurable_storeyPi0Plus1_comp {Y : Type*} [MeasurableSpace Y] (x : Y → Fin m → ℝ)
    (hx : ∀ j, Measurable fun y => x y j) (lam : ℝ) :
    Measurable fun y => storeyPi0Plus1 lam (x y) := by
  unfold storeyPi0Plus1
  exact (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_numAbove_comp x hx lam)).add_const 1).div_const _

private theorem measurable_storeyBHIndex_comp {Y : Type*} [MeasurableSpace Y] (q lam : ℝ)
    (x : Y → Fin m → ℝ) (hx : ∀ j, Measurable fun y => x y j) :
    Measurable fun y => storeyBHIndex q lam (x y) := by
  refine measurable_suIdx_comp (fun y => storeyThreshold q lam (x y)) x (fun k => ?_) hx
  unfold storeyThreshold
  exact measurable_const.min
    (((measurable_storeyPi0Plus1_comp x hx lam).const_div q).mul_const _ |>.div_const _)

/-! ### Leave-one-out bookkeeping -/

/-- Rebuild a full p-value vector from the coordinates other than `i`, putting `0` at `i`. -/
private noncomputable def fillZero (i : Fin m) (y : {j // j ≠ i} → ℝ) : Fin m → ℝ :=
  fun j => if h : j = i then 0 else y ⟨j, h⟩

private theorem measurable_fillZero (i : Fin m) (j : Fin m) :
    Measurable fun y : {j // j ≠ i} → ℝ => fillZero i y j := by
  by_cases h : j = i
  · simp only [fillZero, h, dite_true]
    exact measurable_const
  · simp only [fillZero, h, dite_false]
    exact measurable_pi_apply (⟨j, h⟩ : {j // j ≠ i})

private theorem fillZero_rest (i : Fin m) (p : Fin m → ℝ) :
    fillZero i (fun j : {j // j ≠ i} => p j) = Function.update p i 0 := by
  funext j
  by_cases h : j = i
  · subst h; simp [fillZero]
  · simp [fillZero, h]

/-- Number of p-values other than `p i` that exceed `lam` (computed on `p` with `p i := 0`). -/
private noncomputable def numAboveLOO (lam : ℝ) (p : Fin m → ℝ) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun j => lam < Function.update p i 0 j).card

private theorem numAboveLOO_lt {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin m → ℝ) (i : Fin m) :
    numAboveLOO lam p i < m := by
  classical
  have hsub : (Finset.univ.filter fun j => lam < Function.update p i 0 j) ⊆
      Finset.univ.erase i := by
    intro j hj
    have hj := (Finset.mem_filter.mp hj).2
    refine Finset.mem_erase.mpr ⟨fun hji => ?_, Finset.mem_univ _⟩
    subst hji
    simp at hj
    linarith
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  unfold numAboveLOO
  have := i.isLt
  omega

private theorem numAboveLOO_add_one {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin m → ℝ) (i : Fin m)
    (hpi : lam < p i) :
    numAboveLOO lam p i + 1 = (Finset.univ.filter fun j => lam < p j).card := by
  classical
  have hmem : i ∈ Finset.univ.filter fun j => lam < p j := by simpa using hpi
  have heq : (Finset.univ.filter fun j => lam < Function.update p i 0 j) =
      (Finset.univ.filter fun j => lam < p j).erase i := by
    ext j
    by_cases hji : j = i
    · subst hji; simp [not_lt.mpr hlam]
    · simp [hji]
  unfold numAboveLOO
  rw [heq, Finset.card_erase_of_mem hmem]
  have := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

private theorem storeyThreshold_update_eq (hm : m ≠ 0) (q lam : ℝ) (p : Fin m → ℝ) (i : Fin m)
    (k : ℕ) : storeyThreshold q lam (Function.update p i 0) k =
      min lam (q * (1 - lam) * k / ((numAboveLOO lam p i : ℝ) + 1)) := by
  rw [storeyThreshold_eq hm]
  rfl

/-- The FDP as a sum over true nulls of the per-hypothesis contributions. -/
private theorem fdp_eq_sum (H0 R : Finset (Fin m)) :
    falseDiscoveryProportion H0 R =
      ∑ i ∈ H0, if i ∈ R then 1 / max (R.card : ℝ) 1 else 0 := by
  classical
  have hc : ((R ∩ H0).card : ℝ) = ∑ i ∈ H0, if i ∈ R then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [falseDiscoveryProportion, hc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

/-- The capped adaptive threshold as a function of `(k, n)`, `n` = number of other p-values above
`lam`. -/
private noncomputable def theta (q lam : ℝ) (x : ℕ × ℕ) : ℝ :=
  min lam (q * (1 - lam) * x.1 / ((x.2 : ℝ) + 1))

/-- The contribution of hypothesis `i` to the FDP, as a finite sum of indicators of events
`{p i ≤ θ(k, n), K = k, N = n}` where `K` and `N` depend only on the other p-values. -/
private theorem contribution_eq_sum {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (p : Fin m → ℝ) (i : Fin m) :
    (if i ∈ storeyBHRejections q lam p then 1 / max ((storeyBHRejections q lam p).card : ℝ) 1
      else 0) =
      ∑ x ∈ Finset.Icc 1 m ×ˢ Finset.range m,
        if p i ≤ theta q lam x ∧
            (storeyBHIndex q lam (Function.update p i 0), numAboveLOO lam p i) = x
          then 1 / (x.1 : ℝ) else 0 := by
  classical
  have hm : m ≠ 0 := by have := i.isLt; omega
  have hthr (k : ℕ) : storeyThreshold q lam (Function.update p i 0) k =
      theta q lam (k, numAboveLOO lam p i) := storeyThreshold_update_eq hm q lam p i k
  have hcard0 := card_storeyBHRejections hq hlam1 (Function.update p i 0)
  by_cases hi : i ∈ storeyBHRejections q lam p
  · set k := (storeyBHRejections q lam p).card with hk
    have hloo := (storeyBH_leave_one_out hq hlam0 hlam1 p i k).mp ⟨hi, rfl⟩
    have hk1 : 1 ≤ k := Finset.card_pos.mpr ⟨i, hi⟩
    have hkm : k ≤ m := by
      rw [hk, card_storeyBHRejections hq hlam1]; exact storeyBHIndex_le q lam p
    rw [hthr, hcard0] at hloo
    rw [Finset.sum_eq_single (k, numAboveLOO lam p i)]
    · simp [hi, hloo.1, hloo.2, max_eq_left (show (1 : ℝ) ≤ k by exact_mod_cast hk1)]
    · intro x _ hx
      refine ite_eq_right_iff.mpr fun ⟨_, hx'⟩ => (hx (by rw [← hx', hloo.2])).elim
    · intro hx
      exact (hx (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkm⟩,
        Finset.mem_range.mpr (numAboveLOO_lt hlam0 p i)⟩)).elim
  · simp only [hi, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro x _
    refine ite_eq_right_iff.mpr fun ⟨hpx, hx⟩ => absurd ?_ hi
    have hx1 : storeyBHIndex q lam (Function.update p i 0) = x.1 := congrArg Prod.fst hx
    have hx2 : numAboveLOO lam p i = x.2 := congrArg Prod.snd hx
    have := (storeyBH_leave_one_out hq hlam0 hlam1 p i x.1).mpr
      ⟨by rw [hthr, hx2]; exact hpx, by rw [hcard0, hx1]⟩
    exact this.1

/-! ### The probabilistic argument -/

private theorem valid_measureReal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : IsValidPValue μ X) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    μ.real {ω | X ω ≤ t} ≤ t :=
  ENNReal.toReal_le_of_le_ofReal ht₀ (hX t ⟨ht₀, ht₁⟩)

/-- The pair (Storey-BH index of `p` with `p i := 0`, number of other p-values above `lam`) is a
measurable function of the p-values other than `p i`, hence independent of `p i`. -/
private theorem indepFun_looPair {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Fin m → Ω → ℝ} {i : Fin m} (hp : ∀ j, Measurable (p j))
    (hind : IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ) (q lam : ℝ) :
    Measurable (fun ω => (storeyBHIndex q lam (Function.update (fun j => p j ω) i 0),
        numAboveLOO lam (fun j => p j ω) i)) ∧
      IndepFun (p i) (fun ω => (storeyBHIndex q lam (Function.update (fun j => p j ω) i 0),
        numAboveLOO lam (fun j => p j ω) i)) μ := by
  let g : ({j // j ≠ i} → ℝ) → ℕ × ℕ := fun y =>
    (storeyBHIndex q lam (fillZero i y), (Finset.univ.filter fun j => lam < fillZero i y j).card)
  have hg : Measurable g :=
    (measurable_storeyBHIndex_comp q lam _ (measurable_fillZero i)).prodMk
      (measurable_numAbove_comp _ (measurable_fillZero i) lam)
  have heq : (fun ω => (storeyBHIndex q lam (Function.update (fun j => p j ω) i 0),
      numAboveLOO lam (fun j => p j ω) i)) = g ∘ (fun ω (j : {j // j ≠ i}) => p j ω) := by
    funext ω
    simp only [Function.comp_apply, g, numAboveLOO]
    rw [show (fillZero i fun j : {j // j ≠ i} => p (↑j) ω) = Function.update (fun j => p j ω) i 0
      from fillZero_rest i (fun j => p j ω)]
  rw [heq]
  exact ⟨hg.comp (measurable_pi_iff.mpr fun j => hp j), hind.comp measurable_id hg⟩

/-- **Per-null bound.** Under independence of the true-null p-value `p i` from the other p-values
and validity of `p i`, the expected Storey-BH contribution of `i` is at most
`q E[(1 - lam) / (N_i + 1)]`, where `N_i` is the number of *other* p-values above `lam`. -/
private theorem integral_contribution_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ j, Measurable (p j)) (i : Fin m)
    (hind : IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ)
    (hnull : IsValidPValue μ (p i)) {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) :
    Integrable (fun ω => if i ∈ storeyBHRejections q lam (fun j => p j ω) then
        1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) μ ∧
      ∫ ω, (if i ∈ storeyBHRejections q lam (fun j => p j ω) then
        1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) ∂μ ≤
        q * ∫ ω, (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1) ∂μ := by
  classical
  have hm : m ≠ 0 := by have := i.isLt; omega
  set G : Ω → ℕ × ℕ := fun ω => (storeyBHIndex q lam (Function.update (fun j => p j ω) i 0),
    numAboveLOO lam (fun j => p j ω) i) with hGdef
  obtain ⟨hGm, hindG⟩ := indepFun_looPair (μ := μ) hp hind q lam
  set S := Finset.Icc 1 m ×ˢ Finset.range m with hS
  have hGS (ω : Ω) : G ω ∈ S := by
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, storeyBHIndex_le _ _ _⟩,
      Finset.mem_range.mpr (numAboveLOO_lt hlam0 _ i)⟩
    exact one_le_suIdx_update
      (storeyThreshold_nonneg hq hlam0 hlam1.le (Function.update (fun j => p j ω) i 0))
      (fun j => p j ω) i
  let A : ℕ × ℕ → Set Ω := fun x => {ω | p i ω ≤ theta q lam x} ∩ G ⁻¹' {x}
  have hA (x : ℕ × ℕ) : MeasurableSet (A x) :=
    (measurableSet_le (hp i) measurable_const).inter (hGm (measurableSet_singleton x))
  have hcontr : (fun ω => if i ∈ storeyBHRejections q lam (fun j => p j ω) then
        1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) =
      fun ω => ∑ x ∈ S, (A x).indicator (fun _ => 1 / (x.1 : ℝ)) ω := by
    funext ω
    rw [contribution_eq_sum hq hlam0 hlam1.le]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [A, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff, hGdef]
  have hint : Integrable (fun ω => ∑ x ∈ S, (A x).indicator (fun _ => 1 / (x.1 : ℝ)) ω) μ :=
    integrable_finsetSum _ fun x _ => (integrable_const _).indicator (hA x)
  refine ⟨hcontr ▸ hint, ?_⟩
  -- the right-hand side as a finite sum over the values of `G`
  have hrhs : (fun ω => (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1)) =
      fun ω => ∑ x ∈ S, (G ⁻¹' {x}).indicator (fun _ => (1 - lam) / ((x.2 : ℝ) + 1)) ω := by
    funext ω
    rw [Finset.sum_eq_single (G ω)]
    · simp [hGdef]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro h; exact (h (hGS ω)).elim
  rw [hcontr, hrhs, integral_finsetSum _ fun x _ => (integrable_const _).indicator (hA x),
    integral_finsetSum _ fun x _ =>
      (integrable_const _).indicator (hGm (measurableSet_singleton x)),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [integral_indicator_const _ (hA x),
    integral_indicator_const _ (hGm (measurableSet_singleton x)), smul_eq_mul, smul_eq_mul]
  have hx1 : 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
  have hθ0 : 0 ≤ theta q lam x := le_min hlam0 (by
    have : 0 ≤ 1 - lam := by linarith
    positivity)
  have hθ1 : theta q lam x ≤ 1 := (min_le_left _ _).trans hlam1.le
  have hprod : μ.real (A x) = μ.real {ω | p i ω ≤ theta q lam x} * μ.real (G ⁻¹' {x}) := by
    have h := hindG.measure_inter_preimage_eq_mul (Set.Iic (theta q lam x)) {x}
      measurableSet_Iic (measurableSet_singleton x)
    simpa [A, Set.preimage, measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  have hk : (0 : ℝ) < x.1 := by exact_mod_cast hx1
  calc μ.real (A x) * (1 / (x.1 : ℝ))
      ≤ theta q lam x * μ.real (G ⁻¹' {x}) * (1 / (x.1 : ℝ)) := by
        rw [hprod]
        gcongr
        exact valid_measureReal_le hnull hθ0 hθ1
    _ ≤ (q * (1 - lam) * x.1 / ((x.2 : ℝ) + 1)) * μ.real (G ⁻¹' {x}) * (1 / (x.1 : ℝ)) := by
        gcongr
        exact min_le_right _ _
    _ = q * (μ.real (G ⁻¹' {x}) * ((1 - lam) / ((x.2 : ℝ) + 1))) := by
        field_simp

/-- **The estimator property used by the proof.** If each true-null p-value `p i` is independent
of the other p-values and valid at `lam` (`P(p i ≤ lam) ≤ lam`), then, with `N_i` the number of
p-values other than `p i` above `lam`, `∑_{i ∈ H0} E[(1 - lam) / (N_i + 1)] ≤ 1`.

Proof: independence gives `(1 - lam) E[1/(N_i + 1)] ≤ P(p i > lam) E[1/(N_i + 1)]
= E[1{p i > lam} / (N_i + 1)]`, and on `{p i > lam}`, `N_i + 1` is the total number `A` of p-values
above `lam`, so the sum over `H0` is at most `E[#{i ∈ H0 : p i > lam} / A] ≤ 1`. -/
private theorem sum_integral_loo_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ j, Measurable (p j))
    (H0 : Finset (Fin m))
    (hind : ∀ i ∈ H0, IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ)
    {lam : ℝ} (hnull : ∀ i ∈ H0, μ.real {ω | p i ω ≤ lam} ≤ lam) (hlam0 : 0 ≤ lam) :
    ∑ i ∈ H0, ∫ ω, (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1) ∂μ ≤ 1 := by
  classical
  let f : ℝ → ℝ := (Set.Ioi lam).indicator 1
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioi
  let g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hg : Measurable g := measurable_of_countable g
  let N : Fin m → Ω → ℕ := fun i ω => numAboveLOO lam (fun j => p j ω) i
  have hN (i : Fin m) (hi : i ∈ H0) : Measurable (N i) ∧ IndepFun (p i) (N i) μ := by
    obtain ⟨hm, hI⟩ := indepFun_looPair (μ := μ) hp (hind i hi) 0 lam
    exact ⟨measurable_snd.comp hm, hI.comp measurable_id measurable_snd⟩
  have hfg_int (i : Fin m) (hi : i ∈ H0) :
      Integrable (fun ω => f (p i ω) * g (N i ω)) μ := by
    refine Integrable.of_bound (((hf.comp (hp i)).mul (hg.comp (hN i hi).1)).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : |f (p i ω)| ≤ 1 := by
      simp only [f, Set.indicator_apply]; split_ifs <;> simp
    have h2 : |g (N i ω)| ≤ 1 := by
      simp only [g]
      rw [abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by linarith [(N i ω).cast_nonneg (α := ℝ)]) (by positivity)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (f (p i ω)), abs_nonneg (g (N i ω))]
  -- step 1: per-null comparison via independence
  have hstep (i : Fin m) (hi : i ∈ H0) :
      ∫ ω, (1 - lam) / ((N i ω : ℝ) + 1) ∂μ ≤ ∫ ω, f (p i ω) * g (N i ω) ∂μ := by
    obtain ⟨hNm, hI⟩ := hN i hi
    rw [hI.integral_fun_comp_mul_comp (hp i).aemeasurable hNm.aemeasurable
      hf.aestronglyMeasurable hg.aestronglyMeasurable]
    have hfint : ∫ ω, f (p i ω) ∂μ = μ.real {ω | lam < p i ω} := by
      have : (fun ω => f (p i ω)) = {ω | lam < p i ω}.indicator (fun _ => (1 : ℝ)) := by
        funext ω; simp [f, Set.indicator_apply]
      rw [this, integral_indicator_const _ (measurableSet_lt measurable_const (hp i)),
        smul_eq_mul, mul_one]
    have hcompl : μ.real {ω | lam < p i ω} = 1 - μ.real {ω | p i ω ≤ lam} := by
      rw [← probReal_compl_eq_one_sub (measurableSet_le (hp i) measurable_const)]
      congr 1; ext ω; simp
    have hgint : 0 ≤ ∫ ω, g (N i ω) ∂μ := integral_nonneg fun ω => by positivity
    have hlhs : ∫ ω, (1 - lam) / ((N i ω : ℝ) + 1) ∂μ = (1 - lam) * ∫ ω, g (N i ω) ∂μ := by
      rw [← integral_const_mul]; congr 1; funext ω; simp [g, div_eq_mul_inv]
    rw [hlhs, hfint, hcompl]
    have := hnull i hi
    nlinarith
  -- step 2: the pointwise bound `∑_{i ∈ H0} 1{p i > lam} / (N_i + 1) ≤ 1`
  have hpt (ω : Ω) : ∑ i ∈ H0, f (p i ω) * g (N i ω) ≤ 1 := by
    set A := (Finset.univ.filter fun j => lam < p j ω).card
    have hterm : ∀ i ∈ H0, f (p i ω) * g (N i ω) =
        if lam < p i ω then 1 / (A : ℝ) else 0 := by
      intro i _
      by_cases h : lam < p i ω
      · have := numAboveLOO_add_one hlam0 (fun j => p j ω) i h
        simp only [f, g, N, Set.indicator_apply, Set.mem_Ioi, h, ↓reduceIte, Pi.one_apply,
          one_mul]
        have hA' : (A : ℝ) = (numAboveLOO lam (fun j => p j ω) i : ℝ) + 1 := by
          exact_mod_cast this.symm
        rw [hA']
      · simp [f, h]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle : (H0.filter fun i => lam < p i ω).card ≤ A :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ H0))
    rcases Nat.eq_zero_or_pos A with hA | hA
    · simp [hA]
    · rw [mul_one_div, div_le_one (by exact_mod_cast hA)]
      exact_mod_cast hle
  calc ∑ i ∈ H0, ∫ ω, (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1) ∂μ
      ≤ ∑ i ∈ H0, ∫ ω, f (p i ω) * g (N i ω) ∂μ := Finset.sum_le_sum hstep
    _ = ∫ ω, ∑ i ∈ H0, f (p i ω) * g (N i ω) ∂μ := (integral_finsetSum H0 hfg_int).symm
    _ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono (integrable_finsetSum H0 hfg_int)
        (integrable_const 1) hpt
    _ = 1 := by simp

/-- **Storey-BH controls the FDR at level `q` under independence** (Storey, Taylor and Siegmund
2004, Theorem 3). Let `H0` be the set of true nulls. Assume

* every true-null p-value `p i` is valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`);
* every true-null p-value `p i` is independent of the vector of all other p-values
  `(p j)_{j ≠ i}` (implied by mutual independence, `iIndepFun`; the false-null p-values may be
  arbitrarily dependent among themselves);
* the tuning parameter `lam ∈ [0, 1)` is fixed, i.e. chosen without looking at the data.

Then BH run at the adaptive level `q / π̂₀(lam)`, with Storey's estimator
`π̂₀(lam) = (#{p j > lam} + 1) / ((1 - lam) m)` and thresholds capped at `lam`
(`storeyBHRejections`), has false discovery rate at most `q`, for every `q ≥ 0`.

Unlike plain BH (`E[FDP] ≤ q |H0| / m`), the bound does not shrink with `|H0| / m`: the adaptive
level spends the slack. The proof goes through the interaction of the adaptive threshold with the
p-values, not through `E[π̂₀] ≥ |H0| / m` (which holds, `TwoGroupsTesting.le_integral_storeyPi0`
and `storeyPi0_le_storeyPi0Plus1`, but does not suffice). On `{i rejected}` we have `p i ≤ lam`,
so `π̂₀` does not depend on `p i` and the
leave-one-out property (`storeyBH_leave_one_out`) gives
`E[1{i ∈ R} / |R|] ≤ q (1 - lam) E[1 / (N_i + 1)]`, where `N_i` counts the *other* p-values above
`lam`; then `∑_{i ∈ H0} (1 - lam) E[1 / (N_i + 1)] ≤ 1`
(`sum_integral_inv_storeyPi0Plus1_update_le`). (For `m = 0` both sides are `0`.)

Source: J. D. Storey, J. E. Taylor and D. Siegmund, *Strong control, conservative point
estimation and simultaneous conservative consistency of false discovery rates: a unified
approach*, J. R. Statist. Soc. B 66 (2004), 187–205, Theorem 3; the leave-one-out argument
follows G. Blanchard and É. Roquain, *Adaptive false discovery rate control under independence and
dependence*, J. Mach. Learn. Res. 10 (2009), 2837–2871. -/
theorem integral_falseDiscoveryProportion_storeyBHRejections_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m))
    (hindep : ∀ i ∈ H0, IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ)
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i))
    {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    ∫ ω, falseDiscoveryProportion H0 (storeyBHRejections q lam fun i => p i ω) ∂μ ≤ q := by
  classical
  have hc (i : Fin m) (hi : i ∈ H0) :=
    integral_contribution_le μ p hp i (hindep i hi) (hnull i hi) hq hlam0 hlam1
  have hsum := sum_integral_loo_le_one μ p hp H0 hindep
    (fun i hi => valid_measureReal_le (hnull i hi) hlam0 hlam1.le) hlam0
  calc ∫ ω, falseDiscoveryProportion H0 (storeyBHRejections q lam fun i => p i ω) ∂μ
      = ∫ ω, ∑ i ∈ H0, (if i ∈ storeyBHRejections q lam (fun j => p j ω) then
          1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) ∂μ := by
        congr 1; funext ω; exact fdp_eq_sum _ _
    _ = ∑ i ∈ H0, ∫ ω, (if i ∈ storeyBHRejections q lam (fun j => p j ω) then
          1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) ∂μ :=
        integral_finsetSum H0 fun i hi => (hc i hi).1
    _ ≤ ∑ i ∈ H0, q * ∫ ω, (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1) ∂μ :=
        Finset.sum_le_sum fun i hi => (hc i hi).2
    _ = q * ∑ i ∈ H0, ∫ ω, (1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1) ∂μ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ q * 1 := mul_le_mul_of_nonneg_left hsum hq
    _ = q := mul_one q

/-- **The property of Storey's estimator that the FDR proof uses.** Let `π̂₀⁽ⁱ⁾` be Storey's
estimator computed with `p i` replaced by `0` (equivalently, from the other p-values). If each
true-null p-value is valid and independent of the other p-values, then
`∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m`, for `0 ≤ lam ≤ 1`. Combined with the leave-one-out property this
gives
`E[FDP] ≤ ∑_{i ∈ H0} (q / m) E[1 / π̂₀⁽ⁱ⁾] ≤ q`. This is a bound on the *inverse* of the
leave-one-out estimator; conservativeness in expectation, `E[π̂₀] ≥ |H0| / m`
(`TwoGroupsTesting.le_integral_storeyPi0`), does not imply it (Jensen goes the wrong way). -/
theorem sum_integral_inv_storeyPi0Plus1_update_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (H0 : Finset (Fin m))
    (hindep : ∀ i ∈ H0, IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ)
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∑ i ∈ H0, ∫ ω, (storeyPi0Plus1 lam (Function.update (fun j => p j ω) i 0))⁻¹ ∂μ ≤ m := by
  have heq (i : Fin m) (ω : Ω) : (storeyPi0Plus1 lam (Function.update (fun j => p j ω) i 0))⁻¹ =
      m * ((1 - lam) / ((numAboveLOO lam (fun j => p j ω) i : ℝ) + 1)) := by
    rw [storeyPi0Plus1, inv_div, numAboveLOO]; ring
  simp_rw [heq, integral_const_mul, ← Finset.mul_sum]
  calc (m : ℝ) * _ ≤ m * 1 := mul_le_mul_of_nonneg_left
        (sum_integral_loo_le_one μ p hp H0 hindep
          (fun i hi => valid_measureReal_le (hnull i hi) hlam0 hlam1) hlam0) (Nat.cast_nonneg m)
    _ = m := mul_one _

/-- **Bridge to Storey's (2002) estimator on main.** `storeyPi0Plus1` is
`TwoGroupsTesting.storeyPi0` plus the finite-sample correction `1 / ((1 - lam) m)`. -/
theorem storeyPi0Plus1_eq_storeyPi0_add (lam : ℝ) (p : Fin m → ℝ) :
    storeyPi0Plus1 lam p =
      TwoGroupsTesting.storeyPi0 lam p + 1 / ((1 - lam) * m) := by
  rw [storeyPi0Plus1, TwoGroupsTesting.storeyPi0, add_div, mul_comm (m : ℝ)]

/-- The `+ 1` estimator dominates Storey's (2002) estimator pointwise for `lam ≤ 1`, so the
conservativeness in expectation `TwoGroupsTesting.le_integral_storeyPi0`
(`E[π̂₀] ≥ |H0| / m`) transfers to it. -/
theorem storeyPi0_le_storeyPi0Plus1 {lam : ℝ} (hlam : lam ≤ 1) (p : Fin m → ℝ) :
    TwoGroupsTesting.storeyPi0 lam p ≤ storeyPi0Plus1 lam p := by
  rw [storeyPi0Plus1_eq_storeyPi0_add]
  have : 0 ≤ 1 - lam := by linarith
  have : 0 ≤ 1 / ((1 - lam) * m) := by positivity
  linarith

/-- Mutually independent p-values satisfy the independence hypothesis of the Storey-BH theorem:
each `p i` is independent of the vector of the other p-values. -/
theorem indepFun_rest_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (i : Fin m) :
    IndepFun (p i) (fun ω (j : {j // j ≠ i}) => p j ω) μ := by
  have hST : Disjoint ({i} : Set (Fin m)) {j | j ≠ i} :=
    Set.disjoint_left.mpr fun j hj hj' => hj' (Set.mem_singleton_iff.mp hj)
  exact (iIndepFun.indepFun_set {i} {j | j ≠ i} hST hindep hp).comp
    (measurable_pi_apply (⟨i, Set.mem_singleton i⟩ : ({i} : Set (Fin m)))) measurable_id

/-- **Storey-BH FDR control for mutually independent p-values**: the special case of
`integral_falseDiscoveryProportion_storeyBHRejections_le` under `iIndepFun`.

Source: Storey, Taylor and Siegmund (2004), Theorem 3. -/
theorem integral_falseDiscoveryProportion_storeyBHRejections_le_of_iIndepFun {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i))
    {q lam : ℝ} (hq : 0 ≤ q) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    ∫ ω, falseDiscoveryProportion H0 (storeyBHRejections q lam fun i => p i ω) ∂μ ≤ q :=
  integral_falseDiscoveryProportion_storeyBHRejections_le μ p hp H0
    (fun i _ => indepFun_rest_of_iIndepFun hp hindep i) hnull hq hlam0 hlam1

end MathlibExt.Probability.Statistics.MultipleTesting
