/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialTail
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import MathlibExt.Probability.Statistics.ExactTests.BinomialTest
public import Mathlib.Probability.Distributions.Binomial

/-!
# The Clopper–Pearson exact confidence interval for a binomial proportion

After observing `x` successes in `n` independent trials with unknown success probability
`p ∈ [0, 1]`, the two-sided Clopper–Pearson interval at level `α` inverts the two one-sided
exact binomial tests, giving each tail the error budget `α / 2`:

* the lower endpoint `L(x) = inf {p ∈ [0, 1] | α / 2 ≤ P_p(X ≥ x)}`;
* the upper endpoint `U(x) = sup {p ∈ [0, 1] | α / 2 ≤ P_p(X ≤ x)}`.

Here `P_p(X ≥ x) = binomTail n x p` is the binomial upper tail, and
`P_p(X ≤ x) = 1 - binomTail n (x + 1) p`. Because the upper tail is continuous and strictly
increasing in `p` for `1 ≤ x ≤ n`, `L(x)` is the root of `P_p(X ≥ x) = α / 2` for `x > 0`, and
`U(x)` is the root of `P_p(X ≤ x) = α / 2` for `x < n`. The boundary conventions `L(0) = 0` and
`U(n) = 1` are theorems of the same definitions, not separate branches.

The interval covers the true `p` with probability at least `1 - α`, for every `n` and `p`. The
proof needs only the inversion direction: if `p < L(X)` then the upper-tail p-value of `X` is
below `α / 2`, and if `U(X) < p` then the lower-tail p-value is; each event has probability at
most `α / 2` because tail p-values of a discrete law are valid. Coverage is at least, not
exactly, `1 - α`, since the binomial law has atoms.

## Main definitions

* `clopperPearsonLower n x α`, `clopperPearsonUpper n x α`: the endpoints `L(x)`, `U(x)`.

## Main results

* `clopperPearson_coverage`: **coverage**, `1 - α ≤ P(L(X) ≤ p ≤ U(X))` for `X ~ Bin(n, p)`.
* `clopperPearsonLower_coverage`, `clopperPearsonUpper_coverage`: the one-sided bounds, each
  with coverage at least `1 - α / 2`.
* `binomTail_clopperPearsonLower`, `binomTail_clopperPearsonUpper`: the endpoints solve the
  tail equations `P_L(X ≥ x) = α / 2` (`x > 0`) and `P_U(X ≤ x) = α / 2` (`x < n`), with the
  measure forms `upperTail_binomial_clopperPearsonLower` and
  `binomial_real_Iic_clopperPearsonUpper`.
* `clopperPearsonLower_le_iff`, `le_clopperPearsonUpper_iff`: test inversion,
  `L(x) ≤ p ↔ α / 2 ≤ P_p(X ≥ x)` and `p ≤ U(x) ↔ α / 2 ≤ P_p(X ≤ x)`.
* `clopperPearsonLower_zero`, `clopperPearsonUpper_self`: `L(0) = 0`, `U(n) = 1`.
* `clopperPearsonLower_mem_Icc`, `clopperPearsonUpper_mem_Icc`,
  `clopperPearsonLower_le_clopperPearsonUpper`, `clopperPearsonLower_mono`,
  `clopperPearsonUpper_mono`: both endpoints lie in `[0, 1]`, `L(x) ≤ U(x)` for `α ≤ 1`, and
  both endpoints are nondecreasing in `x`.

## Conventions

The level is `0 < α < 1`, split equally between the two tails. The endpoints are defined for
every `n`, `x` and `α`; for `x > n` they are junk values. The binomial tails are taken from
`binomTail` (`MathlibExt.Probability.Distributions.BinomialTail`) and connected to Mathlib's
`binomial` measure by `upperTail_binomial` and `binomial_real_Iic`
(both `ExactTests.BinomialTest`).

## References

* C. J. Clopper and E. S. Pearson, *The use of confidence or fiducial limits illustrated in the
  case of the binomial*, Biometrika 26 (1934), 404–413.
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Probability.Statistics.ExactTests

/-! ### The endpoints -/

/-- **Clopper–Pearson lower endpoint** after `x` successes in `n` trials at level `α`:
`L(x) = inf {p ∈ [0, 1] | α / 2 ≤ P_p(X ≥ x)}`. For `0 < α < 2` and `1 ≤ x ≤ n` it is the root of
`P_p(X ≥ x) = α / 2` (`binomTail_clopperPearsonLower`); `L(0) = 0`
(`clopperPearsonLower_zero`). -/
noncomputable def clopperPearsonLower (n x : ℕ) (α : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Icc 0 1 ∧ α / 2 ≤ binomTail n x p}

/-- **Clopper–Pearson upper endpoint** after `x` successes in `n` trials at level `α`:
`U(x) = sup {p ∈ [0, 1] | α / 2 ≤ P_p(X ≤ x)}`, where `P_p(X ≤ x) = 1 - binomTail n (x + 1) p`.
For `0 < α < 2` and `x < n` it is the root of `P_p(X ≤ x) = α / 2`
(`binomTail_clopperPearsonUpper`); `U(n) = 1` (`clopperPearsonUpper_self`). -/
noncomputable def clopperPearsonUpper (n x : ℕ) (α : ℝ) : ℝ :=
  sSup {p : ℝ | p ∈ Icc 0 1 ∧ α / 2 ≤ 1 - binomTail n (x + 1) p}

/-- A probability whose upper tail is at least `α / 2` is at least the lower endpoint. -/
theorem clopperPearsonLower_le_of_le_binomTail {n x : ℕ} {α p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (h : α / 2 ≤ binomTail n x p) : clopperPearsonLower n x α ≤ p :=
  csInf_le ⟨0, fun _ hq => hq.1.1⟩ ⟨hp, h⟩

/-- A probability whose lower tail is at least `α / 2` is at most the upper endpoint. -/
theorem le_clopperPearsonUpper_of_le {n x : ℕ} {α p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (h : α / 2 ≤ 1 - binomTail n (x + 1) p) : p ≤ clopperPearsonUpper n x α :=
  le_csSup ⟨1, fun _ hq => hq.1.2⟩ ⟨hp, h⟩

/-- The lower endpoint lies in `[0, 1]`. -/
theorem clopperPearsonLower_mem_Icc (n x : ℕ) (α : ℝ) :
    clopperPearsonLower n x α ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Real.sInf_nonneg fun _ hq => hq.1.1, ?_⟩
  rcases Set.eq_empty_or_nonempty {p : ℝ | p ∈ Icc 0 1 ∧ α / 2 ≤ binomTail n x p} with h | ⟨q, hq⟩
  · rw [clopperPearsonLower, h, Real.sInf_empty]
    exact zero_le_one
  · exact (clopperPearsonLower_le_of_le_binomTail hq.1 hq.2).trans hq.1.2

/-- The upper endpoint lies in `[0, 1]`. -/
theorem clopperPearsonUpper_mem_Icc (n x : ℕ) (α : ℝ) :
    clopperPearsonUpper n x α ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.sSup_nonneg fun _ hq => hq.1.1, Real.sSup_le (fun _ hq => hq.1.2) zero_le_one⟩

/-- **`L(0) = 0`**: after no successes the lower endpoint is `0` (for `α ≤ 2`). -/
theorem clopperPearsonLower_zero (n : ℕ) {α : ℝ} (hα : α ≤ 2) : clopperPearsonLower n 0 α = 0 := by
  have hs : {p : ℝ | p ∈ Icc 0 1 ∧ α / 2 ≤ binomTail n 0 p} = Icc 0 1 := by
    ext p
    simp only [mem_ofPred_eq, binomTail_zero, and_iff_left_iff_imp]
    intro _
    linarith
  rw [clopperPearsonLower, hs, csInf_Icc zero_le_one]

/-- **`U(n) = 1`**: after all successes the upper endpoint is `1` (for `α ≤ 2`). -/
theorem clopperPearsonUpper_self (n : ℕ) {α : ℝ} (hα : α ≤ 2) : clopperPearsonUpper n n α = 1 := by
  have hs : {p : ℝ | p ∈ Icc 0 1 ∧ α / 2 ≤ 1 - binomTail n (n + 1) p} = Icc 0 1 := by
    ext p
    simp only [mem_ofPred_eq, binomTail_of_lt (Nat.lt_succ_self n), sub_zero,
      and_iff_left_iff_imp]
    intro _
    linarith
  rw [clopperPearsonUpper, hs, csSup_Icc zero_le_one]

/-! ### Root characterization -/

/-- The binomial upper tail is antitone in the cutoff on `[0, 1]`. -/
private theorem binomTail_anti {n x y : ℕ} (hxy : x ≤ y) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    binomTail n y p ≤ binomTail n x p :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hxy) fun _ _ _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
      (pow_nonneg (sub_nonneg.2 hp.2) _)

/-- For `1 ≤ x ≤ n`, every level `c ∈ (0, 1)` is attained by the upper tail at an interior `p`. -/
private theorem exists_binomTail_eq {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) : ∃ q ∈ Ioo (0 : ℝ) 1, binomTail n x q = c := by
  have hc : c ∈ Icc (binomTail n x 0) (binomTail n x 1) := by
    rw [binomTail_zero_right hx, binomTail_one_right hxn]
    exact ⟨hc0.le, hc1.le⟩
  obtain ⟨q, hq, hroot⟩ :=
    intermediate_value_Icc zero_le_one (continuous_binomTail n x).continuousOn hc
  refine ⟨q, ⟨lt_of_le_of_ne hq.1 ?_, lt_of_le_of_ne hq.2 ?_⟩, hroot⟩
  · rintro rfl
    rw [binomTail_zero_right hx] at hroot
    linarith
  · rintro rfl
    rw [binomTail_one_right hxn] at hroot
    linarith

/-- For `1 ≤ x ≤ n`, the lower-endpoint tail set is `[q, 1]`, where `P_q(X ≥ x) = c`. -/
private theorem lowerSet_eq {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {q c : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hroot : binomTail n x q = c) :
    {p : ℝ | p ∈ Icc 0 1 ∧ c ≤ binomTail n x p} = Icc q 1 := by
  have hmono := strictMonoOn_binomTail hx hxn
  ext p
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨(hmono.le_iff_le hq hp).1 (hroot ▸ h), hp.2⟩
  · rintro ⟨hqp, hp1⟩
    have hp : p ∈ Icc (0 : ℝ) 1 := ⟨hq.1.trans hqp, hp1⟩
    exact ⟨hp, hroot ▸ (hmono.le_iff_le hq hp).2 hqp⟩

/-- For `1 ≤ k ≤ n`, the upper-endpoint tail set is `[0, q]`, where `P_q(X ≥ k) = 1 - a`. -/
private theorem upperSet_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {q a : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hroot : binomTail n k q = 1 - a) :
    {p : ℝ | p ∈ Icc 0 1 ∧ a ≤ 1 - binomTail n k p} = Icc 0 q := by
  have hmono := strictMonoOn_binomTail hk hkn
  ext p
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp.1, (hmono.le_iff_le hp hq).1 (by linarith)⟩
  · rintro ⟨hp0, hpq⟩
    have hp : p ∈ Icc (0 : ℝ) 1 := ⟨hp0, hpq.trans hq.2⟩
    have := (hmono.le_iff_le hp hq).2 hpq
    exact ⟨hp, by linarith⟩

/-- **Uniqueness of the lower endpoint**: for `1 ≤ x ≤ n`, any `p ∈ [0, 1]` with
`P_p(X ≥ x) = α / 2` is `L(x)`. -/
theorem clopperPearsonLower_eq_of_binomTail_eq {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (h : binomTail n x p = α / 2) : clopperPearsonLower n x α = p := by
  rw [clopperPearsonLower, lowerSet_eq hx hxn hp h, csInf_Icc hp.2]

/-- **Uniqueness of the upper endpoint**: for `x < n`, any `p ∈ [0, 1]` with
`P_p(X ≤ x) = α / 2` is `U(x)`. -/
theorem clopperPearsonUpper_eq_of_binomTail_eq {n x : ℕ} (hxn : x < n) {α p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (h : 1 - binomTail n (x + 1) p = α / 2) :
    clopperPearsonUpper n x α = p := by
  rw [clopperPearsonUpper, upperSet_eq (Nat.le_add_left 1 x) hxn hp (by linarith),
    csSup_Icc hp.1]

/-- **Tail equation at the lower endpoint**: for `1 ≤ x ≤ n` and `0 < α < 2`,
`P_{L(x)}(X ≥ x) = α / 2`. -/
theorem binomTail_clopperPearsonLower {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) : binomTail n x (clopperPearsonLower n x α) = α / 2 := by
  obtain ⟨q, hq, hroot⟩ := exists_binomTail_eq hx hxn (c := α / 2) (by linarith) (by linarith)
  rw [clopperPearsonLower_eq_of_binomTail_eq hx hxn (Ioo_subset_Icc_self hq) hroot, hroot]

/-- **Tail equation at the upper endpoint**: for `x < n` and `0 < α < 2`,
`P_{U(x)}(X ≤ x) = α / 2`. -/
theorem binomTail_clopperPearsonUpper {n x : ℕ} (hxn : x < n) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) : 1 - binomTail n (x + 1) (clopperPearsonUpper n x α) = α / 2 := by
  obtain ⟨q, hq, hroot⟩ :=
    exists_binomTail_eq (Nat.le_add_left 1 x) hxn (c := 1 - α / 2) (by linarith) (by linarith)
  rw [clopperPearsonUpper_eq_of_binomTail_eq hxn (Ioo_subset_Icc_self hq) (by linarith), hroot]
  ring

/-- For `1 ≤ x ≤ n` and `0 < α < 2` the lower endpoint is interior: `0 < L(x) < 1`. -/
theorem clopperPearsonLower_mem_Ioo {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) : clopperPearsonLower n x α ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨q, hq, hroot⟩ := exists_binomTail_eq hx hxn (c := α / 2) (by linarith) (by linarith)
  rwa [clopperPearsonLower_eq_of_binomTail_eq hx hxn (Ioo_subset_Icc_self hq) hroot]

/-- For `x < n` and `0 < α < 2` the upper endpoint is interior: `0 < U(x) < 1`. -/
theorem clopperPearsonUpper_mem_Ioo {n x : ℕ} (hxn : x < n) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) : clopperPearsonUpper n x α ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨q, hq, hroot⟩ :=
    exists_binomTail_eq (Nat.le_add_left 1 x) hxn (c := 1 - α / 2) (by linarith) (by linarith)
  rwa [clopperPearsonUpper_eq_of_binomTail_eq hxn (Ioo_subset_Icc_self hq) (by linarith)]

/-- The tail equation at the lower endpoint for Mathlib's binomial law:
`Bin(n, L(x))([x, ∞)) = α / 2` for `1 ≤ x ≤ n` and `0 < α < 2`. -/
theorem upperTail_binomial_clopperPearsonLower {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    upperTail (binomial n ⟨_, clopperPearsonLower_mem_Icc n x α⟩) x = α / 2 := by
  rw [upperTail_binomial]
  exact binomTail_clopperPearsonLower hx hxn hα0 hα2

/-- The tail equation at the upper endpoint for Mathlib's binomial law:
`Bin(n, U(x))([0, x]) = α / 2` for `x < n` and `0 < α < 2`. -/
theorem binomial_real_Iic_clopperPearsonUpper {n x : ℕ} (hxn : x < n) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) :
    (binomial n ⟨_, clopperPearsonUpper_mem_Icc n x α⟩).real (Iic x) = α / 2 := by
  rw [binomial_real_Iic]
  exact binomTail_clopperPearsonUpper hxn hα0 hα2

/-! ### Test inversion -/

/-- **Inversion of the upper-tail test**: for `x ≤ n`, `0 < α < 2` and `p ∈ [0, 1]`,
`L(x) ≤ p ↔ α / 2 ≤ P_p(X ≥ x)`. -/
theorem clopperPearsonLower_le_iff {n x : ℕ} (hxn : x ≤ n) {α p : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hp : p ∈ Icc (0 : ℝ) 1) : clopperPearsonLower n x α ≤ p ↔ α / 2 ≤ binomTail n x p := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [clopperPearsonLower_zero n hα2.le, binomTail_zero]
    exact ⟨fun _ => by linarith, fun _ => hp.1⟩
  obtain ⟨q, hq, hroot⟩ := exists_binomTail_eq hx hxn (c := α / 2) (by linarith) (by linarith)
  rw [clopperPearsonLower_eq_of_binomTail_eq hx hxn (Ioo_subset_Icc_self hq) hroot, ← hroot]
  exact ((strictMonoOn_binomTail hx hxn).le_iff_le (Ioo_subset_Icc_self hq) hp).symm

/-- **Inversion of the lower-tail test**: for `x ≤ n`, `0 < α < 2` and `p ∈ [0, 1]`,
`p ≤ U(x) ↔ α / 2 ≤ P_p(X ≤ x)`. -/
theorem le_clopperPearsonUpper_iff {n x : ℕ} (hxn : x ≤ n) {α p : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    p ≤ clopperPearsonUpper n x α ↔ α / 2 ≤ 1 - binomTail n (x + 1) p := by
  rcases hxn.eq_or_lt with rfl | hxn
  · rw [clopperPearsonUpper_self x hα2.le, binomTail_of_lt (Nat.lt_succ_self x)]
    exact ⟨fun _ => by linarith, fun _ => hp.2⟩
  obtain ⟨q, hq, hroot⟩ :=
    exists_binomTail_eq (Nat.le_add_left 1 x) hxn (c := 1 - α / 2) (by linarith) (by linarith)
  rw [clopperPearsonUpper_eq_of_binomTail_eq hxn (Ioo_subset_Icc_self hq) (by linarith)]
  have := (strictMonoOn_binomTail (Nat.le_add_left 1 x) hxn).le_iff_le hp
    (Ioo_subset_Icc_self hq)
  constructor
  · intro h
    linarith [this.2 h]
  · intro h
    exact this.1 (by linarith)

/-! ### Order and monotonicity -/

/-- **The interval is nonempty**: `L(x) ≤ U(x)` for `x ≤ n` and `0 < α ≤ 1`. -/
theorem clopperPearsonLower_le_clopperPearsonUpper {n x : ℕ} (hxn : x ≤ n) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) : clopperPearsonLower n x α ≤ clopperPearsonUpper n x α := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [clopperPearsonLower_zero n (by linarith)]
    exact (clopperPearsonUpper_mem_Icc n 0 α).1
  have hL := clopperPearsonLower_mem_Icc n x α
  refine le_clopperPearsonUpper_of_le hL ?_
  have h1 := binomTail_anti (n := n) (Nat.le_succ x) hL
  have h2 := binomTail_clopperPearsonLower hx hxn hα0 (by linarith)
  linarith

/-- The lower endpoint is nondecreasing in the number of successes, up to `n`. -/
theorem clopperPearsonLower_mono {n x y : ℕ} (hxy : x ≤ y) (hyn : y ≤ n) {α : ℝ} (hα : α ≤ 2) :
    clopperPearsonLower n x α ≤ clopperPearsonLower n y α := by
  refine csInf_le_csInf ⟨0, fun _ hq => hq.1.1⟩ ⟨1, ⟨⟨zero_le_one, le_rfl⟩, ?_⟩⟩ ?_
  · rw [binomTail_one_right hyn]
    linarith
  · rintro p ⟨hp, h⟩
    exact ⟨hp, h.trans (binomTail_anti hxy hp)⟩

/-- The upper endpoint is nondecreasing in the number of successes. -/
theorem clopperPearsonUpper_mono {n x y : ℕ} (hxy : x ≤ y) {α : ℝ} (hα : α ≤ 2) :
    clopperPearsonUpper n x α ≤ clopperPearsonUpper n y α := by
  refine csSup_le_csSup ⟨1, fun _ hq => hq.1.2⟩ ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ?_⟩⟩ ?_
  · rw [binomTail_zero_right (Nat.le_add_left 1 x)]
    linarith
  · rintro p ⟨hp, h⟩
    exact ⟨hp, h.trans (by linarith [binomTail_anti (n := n) (Nat.add_le_add_right hxy 1) hp])⟩

/-! ### Coverage -/

/-- Validity of the lower-tail p-value of a law on `ℕ`, strict form:
`ν {k | ν [0, k] < s} ≤ s` whenever `0 ≤ s` and some `ν [0, k]` reaches `s`. -/
private theorem measureReal_lowerTail_lt_le {ν : Measure ℕ} [IsProbabilityMeasure ν] {s : ℝ}
    (hs0 : 0 ≤ s) (hs : ∃ k, s ≤ ν.real (Iic k)) : ν.real {k | ν.real (Iic k) < s} ≤ s := by
  classical
  have hset : {k | ν.real (Iic k) < s} = Iio (Nat.find hs) := by
    ext k
    simp only [mem_ofPred_eq, mem_Iio]
    constructor
    · intro hk
      by_contra h
      have := measureReal_mono (μ := ν) (Iic_subset_Iic.2 (not_lt.1 h))
      linarith [Nat.find_spec hs]
    · intro hk
      exact not_le.1 (Nat.find_min hs hk)
  rw [hset]
  rcases Nat.eq_zero_or_pos (Nat.find hs) with h | h
  · rw [h]
    simpa using hs0
  · have hI : Iio (Nat.find hs) = Iic (Nat.find hs - 1) := by
      ext k
      simp only [mem_Iio, mem_Iic]
      omega
    rw [hI]
    exact (not_le.1 (Nat.find_min hs (by omega : Nat.find hs - 1 < Nat.find hs))).le

/-- Validity of the upper-tail p-value of a law on `ℕ`, strict form, from
`isValidPValue_upperTailPValue`: `ν {k | ν [k, ∞) < s} ≤ s` for `s ∈ [0, 1]`. -/
private theorem measureReal_upperTail_lt_le {ν : Measure ℕ} [IsProbabilityMeasure ν] {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ν.real {k | upperTail ν k < s} ≤ s := by
  have h := isValidPValue_upperTailPValue (μ := ν) HasLaw.id s hs
  refine (measureReal_mono (μ := ν) fun k (hk : upperTail ν k < s) => hk.le).trans ?_
  exact ENNReal.toReal_le_of_le_ofReal hs.1 h

/-- Under `Bin(n, p)`, the lower endpoint exceeds `p` with probability at most `α / 2`. -/
private theorem binomial_real_lt_clopperPearsonLower_le (n : ℕ) (p : unitInterval) {α : ℝ}
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    (binomial n p).real {k | (p : ℝ) < clopperPearsonLower n k α} ≤ α / 2 := by
  refine (measureReal_mono (μ := binomial n p) fun k (hk : (p : ℝ) < _) => ?_).trans
    (measureReal_upperTail_lt_le ⟨by linarith, by linarith⟩)
  change upperTail (binomial n p) k < α / 2
  rw [upperTail_binomial]
  by_contra h
  exact (not_le.2 hk) (clopperPearsonLower_le_of_le_binomTail p.2 (not_lt.1 h))

/-- Under `Bin(n, p)`, the upper endpoint falls below `p` with probability at most `α / 2`. -/
private theorem binomial_real_clopperPearsonUpper_lt_le (n : ℕ) (p : unitInterval) {α : ℝ}
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    (binomial n p).real {k | clopperPearsonUpper n k α < p} ≤ α / 2 := by
  have hex : ∃ k, α / 2 ≤ (binomial n p).real (Iic k) :=
    ⟨n, by rw [binomial_real_Iic, binomTail_of_lt (Nat.lt_succ_self n)]; linarith⟩
  refine (measureReal_mono (μ := binomial n p) fun k (hk : _ < (p : ℝ)) => ?_).trans
    (measureReal_lowerTail_lt_le (by linarith) hex)
  change (binomial n p).real (Iic k) < α / 2
  rw [binomial_real_Iic]
  by_contra h
  exact (not_le.2 hk) (le_clopperPearsonUpper_of_le p.2 (not_lt.1 h))

/-- **One-sided coverage of the lower endpoint**: if `X ~ Bin(n, p)` and `0 < α < 1`, then
`P(L(X) ≤ p) ≥ 1 - α / 2`. -/
theorem clopperPearsonLower_coverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {p : unitInterval} {X : Ω → ℕ} (hX : HasLaw X (binomial n p) P) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α / 2 ≤ P.real {ω | clopperPearsonLower n (X ω) α ≤ p} := by
  rw [hX.measureReal_eq (p := fun k => clopperPearsonLower n k α ≤ p) (.of_discrete)]
  have hc : {k | clopperPearsonLower n k α ≤ p} = {k | (p : ℝ) < clopperPearsonLower n k α}ᶜ := by
    ext k
    simp
  rw [hc, probReal_compl_eq_one_sub (.of_discrete)]
  linarith [binomial_real_lt_clopperPearsonLower_le n p (α := α) hα0.le (by linarith)]

/-- **One-sided coverage of the upper endpoint**: if `X ~ Bin(n, p)` and `0 < α < 1`, then
`P(p ≤ U(X)) ≥ 1 - α / 2`. -/
theorem clopperPearsonUpper_coverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {p : unitInterval} {X : Ω → ℕ} (hX : HasLaw X (binomial n p) P) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α / 2 ≤ P.real {ω | (p : ℝ) ≤ clopperPearsonUpper n (X ω) α} := by
  rw [hX.measureReal_eq (p := fun k => (p : ℝ) ≤ clopperPearsonUpper n k α) (.of_discrete)]
  have hc : {k | (p : ℝ) ≤ clopperPearsonUpper n k α} = {k | clopperPearsonUpper n k α < p}ᶜ := by
    ext k
    simp
  rw [hc, probReal_compl_eq_one_sub (.of_discrete)]
  linarith [binomial_real_clopperPearsonUpper_lt_le n p (α := α) hα0.le (by linarith)]

/-- **Coverage of the Clopper–Pearson interval**: if `X ~ Bin(n, p)` and `0 < α < 1`, then
`P(L(X) ≤ p ≤ U(X)) ≥ 1 - α`, for every `n` and every `p ∈ [0, 1]`.

Non-coverage means `p < L(X)` or `U(X) < p`; each event forces the corresponding exact tail
p-value below `α / 2`, which has probability at most `α / 2`.

Source: Clopper–Pearson (1934); Casella–Berger (2002), §9.2.3. -/
theorem clopperPearson_coverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {p : unitInterval} {X : Ω → ℕ} (hX : HasLaw X (binomial n p) P) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ P.real {ω | clopperPearsonLower n (X ω) α ≤ p ∧
      (p : ℝ) ≤ clopperPearsonUpper n (X ω) α} := by
  rw [hX.measureReal_eq
    (p := fun k => clopperPearsonLower n k α ≤ p ∧ (p : ℝ) ≤ clopperPearsonUpper n k α)
    (.of_discrete)]
  have hc : {k | clopperPearsonLower n k α ≤ p ∧ (p : ℝ) ≤ clopperPearsonUpper n k α} =
      ({k | (p : ℝ) < clopperPearsonLower n k α} ∪ {k | clopperPearsonUpper n k α < p})ᶜ := by
    ext k
    simp
  rw [hc, probReal_compl_eq_one_sub (.of_discrete)]
  linarith [measureReal_union_le (μ := binomial n p) {k | (p : ℝ) < clopperPearsonLower n k α}
      {k | clopperPearsonUpper n k α < p},
    binomial_real_lt_clopperPearsonLower_le n p (α := α) hα0.le (by linarith),
    binomial_real_clopperPearsonUpper_lt_le n p (α := α) hα0.le (by linarith)]

end MathlibExt.Probability.Statistics.ExactTests
