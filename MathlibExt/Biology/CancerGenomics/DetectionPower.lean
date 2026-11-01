/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.CancerGenomics.Absolute
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# ABSOLUTE detection power for somatic point mutations

Carter et al. (2012, Online Methods, Eq. 9) compute the power to detect a mutation with allelic
fraction `f` at a locus covered by `n` reads. Under the null, a given non-reference base appears
on each read independently with probability `p₀ = ε / 3` (`ε` the sequencing error rate), so the
number of supporting reads is `Bin(n, p₀)`; under the alternative it is `Bin(n, f)`. With
`P(m) = ℙ_{p₀}(X ≥ m)`, the critical count is the least `k` with `P(k) ≤ FPR`, and the test is
randomized at one boundary point with probability `d = (FPR - P(k)) / (P(k - 1) - P(k))`.

**The boundary point is `k - 1`.** Since `P(k - 1) - P(k) = Binom(k - 1 | n, p₀)`, the test
"reject if `X ≥ k`; reject with probability `d` if `X = k - 1`" has size exactly `FPR`
(`power_self`), and its power is `Pow(n, f) = P_f(X ≥ k) + d Binom(k - 1 | n, f)`. The PMC
rendering of Eq. 9 multiplies `d` by `Binom(k | n, f)`; with that reading the size is not `FPR`
in general (the test file has a counterexample), so we formalize the exact-size reading.

## Main results

* `sum_binomPmf`, `upperTail_eq_one_sub_sum`: the binomial law sums to one, and `upperTail`
  agrees with Carter's `P(m) = 1 - ∑_{i < m} Binom(i | n, p)`.
* `upperTail_mono`: binomial upper tails increase with the success probability on `[0, 1]`.
* `binomPmf_le_binomPmf_of_le_div`, `binomPmf_le_binomPmf_of_div_le`: `p ↦ Binom(a | n, p)`
  increases on `[0, a / n]` and decreases on `[a / n, 1]`.
* `randomization_mem`: `0 ≤ d < 1`.
* `power_self`: **exact size**, `Pow(n, p₀) = FPR` for `0 ≤ FPR < 1`.
* `power_mono`: power increases with the allelic fraction.
* `power_somaticAF_mono_purity`, `power_somaticAF_anti_copy`, `power_somaticAF_mono_mult`:
  at the ABSOLUTE allelic fraction `α s / (α q + 2 (1 - α))` (Eq. 2, Eq. 10 for `s = 1`), power
  increases with purity and multiplicity and decreases with local copy number.

## References

* S. L. Carter et al., *Absolute quantification of somatic DNA alterations in human cancer*,
  Nat. Biotechnol. 30 (2012), 413–421 (Online Methods, Eqs. 9, 10).
-/

@[expose] public section

namespace MathlibExt.Biology.CancerGenomics.DetectionPower

open Finset MathlibExt.Biology.CancerGenomics.Absolute

/-- The binomial probability `C(n, i) p^i (1 - p)^(n - i)` of `i` successes in `n` trials, as a
function of `i : ℕ`. It vanishes for `i > n` (the binomial coefficient is zero there, so the
truncated subtraction `n - i` is harmless). -/
def binomPmf (n : ℕ) (p : ℝ) (i : ℕ) : ℝ := (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- The binomial upper tail `ℙ_p(X ≥ m) = ∑_{m ≤ i ≤ n} C(n, i) p^i (1 - p)^(n - i)`, Carter's
`P(m)` with `p = ε / 3`. -/
def upperTail (n : ℕ) (p : ℝ) (m : ℕ) : ℝ := ∑ i ∈ Ico m (n + 1), binomPmf n p i

/-- Binomial probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem binomPmf_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    0 ≤ binomPmf n p i := by
  unfold binomPmf
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- Binomial probabilities are positive on `{0, …, n}` for `0 < p < 1`. -/
theorem binomPmf_pos {n i : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hi : i ≤ n) :
    0 < binomPmf n p i := by
  unfold binomPmf
  have : 0 < 1 - p := by linarith
  have : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos hi
  positivity

/-- Binomial probabilities vanish above `n`. -/
theorem binomPmf_eq_zero {n i : ℕ} (p : ℝ) (hi : n < i) : binomPmf n p i = 0 := by
  simp [binomPmf, Nat.choose_eq_zero_of_lt hi]

/-- The binomial law sums to one (the binomial theorem), for every real `p`. -/
theorem sum_binomPmf (n : ℕ) (p : ℝ) : ∑ i ∈ range (n + 1), binomPmf n p i = 1 := by
  have := (add_pow p (1 - p) n).symm
  simp only [add_sub_cancel, one_pow] at this
  rw [← this]
  refine sum_congr rfl fun i _ => ?_
  unfold binomPmf
  ring

/-- Tail probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem upperTail_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    0 ≤ upperTail n p m :=
  sum_nonneg fun i _ => binomPmf_nonneg hp0 hp1 i

/-- `P(0) = 1`, for every real `p`. -/
theorem upperTail_zero (n : ℕ) (p : ℝ) : upperTail n p 0 = 1 := by
  rw [upperTail, ← range_eq_Ico, sum_binomPmf]

/-- `P(m) = 0` for `m > n`. -/
theorem upperTail_eq_zero {n m : ℕ} (p : ℝ) (hm : n < m) : upperTail n p m = 0 := by
  rw [upperTail, Ico_eq_empty_of_le (by omega), sum_empty]

/-- Carter's form of the tail: `P(m) = 1 - ∑_{i < m} Binom(i | n, p)`, for every `m`. -/
theorem upperTail_eq_one_sub_sum (n : ℕ) (p : ℝ) (m : ℕ) :
    upperTail n p m = 1 - ∑ i ∈ range m, binomPmf n p i := by
  rcases le_or_gt m (n + 1) with hm | hm
  · rw [← sum_binomPmf n p, ← sum_range_add_sum_Ico _ hm, upperTail]
    ring
  · rw [upperTail_eq_zero p (by omega), ← sum_binomPmf n p, ← sum_range_add_sum_Ico _ hm.le]
    rw [sum_eq_zero (s := Ico (n + 1) m) fun i hi => binomPmf_eq_zero p
      (by have := (mem_Ico.1 hi).1; omega)]
    ring

/-- One step of the tail recursion: `P(m) = Binom(m | n, p) + P(m + 1)`. -/
theorem upperTail_eq_add (n : ℕ) (p : ℝ) (m : ℕ) :
    upperTail n p m = binomPmf n p m + upperTail n p (m + 1) := by
  rw [upperTail_eq_one_sub_sum, upperTail_eq_one_sub_sum, sum_range_succ]
  ring

/-- `m ↦ P(m)` is antitone for `0 ≤ p ≤ 1`. -/
theorem upperTail_antitone {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Antitone (upperTail n p) :=
  antitone_nat_of_succ_le fun m => by
    rw [upperTail_eq_add n p m]
    linarith [binomPmf_nonneg (n := n) hp0 hp1 m]

private noncomputable def tailPolynomial (n m : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Ico m (n + 1), bernsteinPolynomial ℝ n i

private theorem tailPolynomial_eval (n m : ℕ) (p : ℝ) :
    (tailPolynomial n m).eval p = upperTail n p m := by
  simp [tailPolynomial, upperTail, Polynomial.eval_finsetSum, bernsteinPolynomial,
    binomPmf]

private theorem tailPolynomial_derivative (n k : ℕ) (hk : k ≤ n) :
    (tailPolynomial n (k + 1)).derivative =
      (n : Polynomial ℝ) *
        (bernsteinPolynomial ℝ (n - 1) k - bernsteinPolynomial ℝ (n - 1) n) := by
  rw [tailPolynomial, Polynomial.derivative_sum,
    ← sum_Ico_add' (fun i => (bernsteinPolynomial ℝ n i).derivative) k n 1]
  simp only [bernsteinPolynomial.derivative_succ]
  rw [← mul_sum, sum_Ico_eq_sum_range]
  congr 1
  have h := sum_range_sub' (fun j => bernsteinPolynomial ℝ (n - 1) (k + j)) (n - k)
  simpa [Nat.add_assoc, Nat.add_sub_of_le hk] using h

/-- **Binomial tails increase with the success probability**: for `0 ≤ p ≤ p' ≤ 1`,
`ℙ_p(X ≥ m) ≤ ℙ_{p'}(X ≥ m)`. -/
theorem upperTail_mono {n : ℕ} {p p' : ℝ} (hp0 : 0 ≤ p) (hpp' : p ≤ p') (hp1 : p' ≤ 1)
    (m : ℕ) : upperTail n p m ≤ upperTail n p' m := by
  by_cases hm : m ≤ n
  · cases m with
    | zero =>
      have h : tailPolynomial n 0 = 1 := by
        simpa [tailPolynomial] using bernsteinPolynomial.sum ℝ n
      simp only [← tailPolynomial_eval, h, Polynomial.eval_one, le_refl]
    | succ k =>
      have hn : 0 < n := by omega
      have hd : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
          0 ≤ deriv (fun x => (tailPolynomial n (k + 1)).eval x) x := by
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
        rw [Polynomial.deriv, tailPolynomial_derivative n k (by omega)]
        simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_sub]
        rw [bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : n - 1 < n)]
        simp only [Polynomial.eval_zero, sub_zero]
        have hb : 0 ≤ (bernsteinPolynomial ℝ (n - 1) k).eval x := by
          simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx'.1.le _))
            (pow_nonneg (by linarith [hx'.2]) _)
        exact mul_nonneg (Nat.cast_nonneg _) hb
      have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
        (fun x _ =>
          ((tailPolynomial n (k + 1)).hasDerivAt x).continuousAt.continuousWithinAt)
        (tailPolynomial n (k + 1)).differentiable.differentiableOn hd
      simpa only [tailPolynomial_eval] using
        hmono ⟨hp0, hpp'.trans hp1⟩ ⟨hp0.trans hpp', hp1⟩ hpp'
  · have he : Ico m (n + 1) = ∅ := Ico_eq_empty_of_le (by omega)
    simp [upperTail, he]

private theorem binomPmf_hasDerivAt (n a : ℕ) (x : ℝ) :
    HasDerivAt (fun p => binomPmf n p a)
      ((n.choose a : ℝ) *
        ((a : ℝ) * x ^ (a - 1) * (1 - x) ^ (n - a) -
          x ^ a * (n - a : ℕ) * (1 - x) ^ (n - a - 1))) x := by
  convert (((hasDerivAt_id x).pow a).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n - a))).const_mul
      (n.choose a : ℝ) using 1
  · ext p
    dsimp [binomPmf]
    ring
  · dsimp
    ring

private theorem binomPmf_deriv_mul {n a : ℕ} (ha : a ≤ n) (x : ℝ) :
    x * (1 - x) * deriv (fun p => binomPmf n p a) x =
      binomPmf n x a * ((a : ℝ) - (n : ℝ) * x) := by
  rw [(binomPmf_hasDerivAt n a x).deriv]
  have hn : (n : ℝ) = (a : ℝ) + (n - a : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le ha).symm
  rw [hn]
  simp only [binomPmf]
  generalize n - a = b
  cases a <;> cases b <;> simp [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

/-- **The binomial likelihood is unimodal in `p`, increasing part**: for `a ≤ n` and
`0 ≤ p ≤ p' ≤ a / n`, `Binom(a | n, p) ≤ Binom(a | n, p')`. -/
theorem binomPmf_le_binomPmf_of_le_div {n a : ℕ} {p p' : ℝ} (ha : a ≤ n) (hp0 : 0 ≤ p)
    (hpp' : p ≤ p') (hp' : p' ≤ a / n) : binomPmf n p a ≤ binomPmf n p' a := by
  by_cases hn : n = 0
  · subst n
    have : a = 0 := by omega
    subst a
    simp [binomPmf]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have har : (a : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast ha)
  have hmono : MonotoneOn (fun p => binomPmf n p a) (Set.Icc 0 ((a : ℝ) / n)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x _ => (binomPmf_hasDerivAt n a x).continuousAt.continuousWithinAt)
      (fun x _ => (binomPmf_hasDerivAt n a x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : x ∈ Set.Ioo 0 ((a : ℝ) / n) := by simpa using hx
    have hx1 : x < 1 := hx'.2.trans_le har
    have hs : 0 ≤ (a : ℝ) - (n : ℝ) * x := by
      have := (le_div_iff₀ hn0).mp hx'.2.le
      nlinarith
    have h := mul_nonneg (binomPmf_nonneg (n := n) hx'.1.le hx1.le a) hs
    rw [← binomPmf_deriv_mul ha x] at h
    exact nonneg_of_mul_nonneg_right h (mul_pos hx'.1 (sub_pos.mpr hx1))
  exact hmono ⟨hp0, hpp'.trans hp'⟩ ⟨hp0.trans hpp', hp'⟩ hpp'

/-- **The binomial likelihood is unimodal in `p`, decreasing part**: for `a ≤ n` and
`a / n ≤ p ≤ p' ≤ 1`, `Binom(a | n, p') ≤ Binom(a | n, p)`. -/
theorem binomPmf_le_binomPmf_of_div_le {n a : ℕ} {p p' : ℝ} (ha : a ≤ n) (hp : a / n ≤ p)
    (hpp' : p ≤ p') (hp1 : p' ≤ 1) : binomPmf n p' a ≤ binomPmf n p a := by
  by_cases hn : n = 0
  · subst n
    have : a = 0 := by omega
    subst a
    simp [binomPmf]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have har : (0 : ℝ) ≤ (a : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
  have hanti : AntitoneOn (fun p => binomPmf n p a) (Set.Icc ((a : ℝ) / n) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x _ => (binomPmf_hasDerivAt n a x).continuousAt.continuousWithinAt)
      (fun x _ => (binomPmf_hasDerivAt n a x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : x ∈ Set.Ioo ((a : ℝ) / n) 1 := by simpa using hx
    have hx0 : 0 < x := har.trans_lt hx'.1
    have hs : (a : ℝ) - (n : ℝ) * x ≤ 0 := by
      have := (div_le_iff₀ hn0).mp hx'.1.le
      nlinarith
    have h := mul_nonpos_of_nonneg_of_nonpos
      (binomPmf_nonneg (n := n) hx0.le hx'.2.le a) hs
    rw [← binomPmf_deriv_mul ha x] at h
    exact nonpos_of_mul_nonpos_right h (mul_pos hx0 (sub_pos.mpr hx'.2))
  exact hanti ⟨hp, hpp'.trans hp1⟩ ⟨hp.trans hpp', hp1⟩ hpp'


/-- Carter's critical count `k = min {m | P(m) ≤ FPR}` for the null success probability
`p₀ = ε / 3` (Online Methods, before Eq. 9). -/
noncomputable def criticalCount (n : ℕ) (p₀ fpr : ℝ) : ℕ := sInf {m | upperTail n p₀ m ≤ fpr}

/-- The randomization probability `d = (FPR - P(k)) / (P(k - 1) - P(k))` of Eq. 9. -/
noncomputable def randomization (n : ℕ) (p₀ fpr : ℝ) : ℝ :=
  (fpr - upperTail n p₀ (criticalCount n p₀ fpr)) /
    (upperTail n p₀ (criticalCount n p₀ fpr - 1) - upperTail n p₀ (criticalCount n p₀ fpr))

/-- The power `Pow(n, f) = P_f(X ≥ k) + d Binom(k - 1 | n, f)` of the exact-size randomized
test (Carter et al. 2012, Eq. 9, with the randomization at `k - 1`; see the module doc). -/
noncomputable def power (n : ℕ) (p₀ fpr f : ℝ) : ℝ :=
  upperTail n f (criticalCount n p₀ fpr) +
    randomization n p₀ fpr * binomPmf n f (criticalCount n p₀ fpr - 1)

/-- The critical count meets the false-positive bound: `P(k) ≤ FPR` (for `FPR ≥ 0`). -/
theorem upperTail_criticalCount_le {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) :
    upperTail n p₀ (criticalCount n p₀ fpr) ≤ fpr :=
  Nat.sInf_mem (s := {m | upperTail n p₀ m ≤ fpr}) ⟨n + 1, by
    simp [upperTail_eq_zero p₀ (Nat.lt_succ_self n), hfpr]⟩

/-- The critical count is at most `n + 1` (for `FPR ≥ 0`). -/
theorem criticalCount_le {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) :
    criticalCount n p₀ fpr ≤ n + 1 :=
  Nat.sInf_le (by simp [upperTail_eq_zero p₀ (Nat.lt_succ_self n), hfpr])

/-- The critical count is positive when `FPR < 1`. -/
theorem criticalCount_pos {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) :
    0 < criticalCount n p₀ fpr := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have := upperTail_criticalCount_le (n := n) (p₀ := p₀) hfpr
  rw [h, upperTail_zero] at this
  linarith

/-- Minimality of the critical count: `FPR < P(k - 1)` (for `0 ≤ FPR < 1`). -/
theorem lt_upperTail_criticalCount_sub_one {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr)
    (hfpr1 : fpr < 1) : fpr < upperTail n p₀ (criticalCount n p₀ fpr - 1) := by
  have hk := criticalCount_pos (n := n) (p₀ := p₀) hfpr hfpr1
  have := Nat.notMem_of_lt_sInf (s := {m | upperTail n p₀ m ≤ fpr})
    (m := criticalCount n p₀ fpr - 1) (by unfold criticalCount at hk ⊢; omega)
  simpa using this

/-- The gap `P(k - 1) - P(k)` is the null probability of the boundary point `k - 1`. -/
theorem upperTail_sub_one_sub {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) :
    upperTail n p₀ (criticalCount n p₀ fpr - 1) - upperTail n p₀ (criticalCount n p₀ fpr) =
      binomPmf n p₀ (criticalCount n p₀ fpr - 1) := by
  have hk := criticalCount_pos (n := n) (p₀ := p₀) hfpr hfpr1
  rw [upperTail_eq_add n p₀ (criticalCount n p₀ fpr - 1), Nat.sub_add_cancel hk]
  ring

/-- **The randomization is a probability**: `0 ≤ d < 1` for `0 ≤ FPR < 1`. -/
theorem randomization_mem {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) :
    0 ≤ randomization n p₀ fpr ∧ randomization n p₀ fpr < 1 := by
  have h1 := upperTail_criticalCount_le (n := n) (p₀ := p₀) hfpr
  have h2 := lt_upperTail_criticalCount_sub_one (n := n) (p₀ := p₀) hfpr hfpr1
  have hden : 0 < upperTail n p₀ (criticalCount n p₀ fpr - 1) -
      upperTail n p₀ (criticalCount n p₀ fpr) := by linarith
  unfold randomization
  refine ⟨div_nonneg (by linarith) hden.le, ?_⟩
  rw [div_lt_one hden]
  linarith

/-- **Exact size** (Carter et al. 2012, Eq. 9 with the randomization at `k - 1`): under the
null `f = p₀` the rejection probability is exactly `FPR`, for `0 ≤ FPR < 1`. -/
theorem power_self {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) :
    power n p₀ fpr p₀ = fpr := by
  have h1 := upperTail_criticalCount_le (n := n) (p₀ := p₀) hfpr
  have h2 := lt_upperTail_criticalCount_sub_one (n := n) (p₀ := p₀) hfpr hfpr1
  have hgap := upperTail_sub_one_sub (n := n) (p₀ := p₀) hfpr hfpr1
  have hden : upperTail n p₀ (criticalCount n p₀ fpr - 1) -
      upperTail n p₀ (criticalCount n p₀ fpr) ≠ 0 := by linarith
  unfold power randomization
  rw [← hgap, div_mul_cancel₀ _ hden]
  ring

/-- The power is the mixture `(1 - d) P_f(X ≥ k) + d P_f(X ≥ k - 1)` of two tail
probabilities. -/
theorem power_eq_mix {n : ℕ} {p₀ fpr : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) (f : ℝ) :
    power n p₀ fpr f = (1 - randomization n p₀ fpr) * upperTail n f (criticalCount n p₀ fpr) +
      randomization n p₀ fpr * upperTail n f (criticalCount n p₀ fpr - 1) := by
  have hk := criticalCount_pos (n := n) (p₀ := p₀) hfpr hfpr1
  unfold power
  rw [upperTail_eq_add n f (criticalCount n p₀ fpr - 1), Nat.sub_add_cancel hk]
  ring

/-- **Power increases with the allelic fraction**: `Pow(n, f) ≤ Pow(n, f')` for
`0 ≤ f ≤ f' ≤ 1`. -/
theorem power_mono {n : ℕ} {p₀ fpr f f' : ℝ} (hfpr : 0 ≤ fpr) (hfpr1 : fpr < 1) (hf0 : 0 ≤ f)
    (hff' : f ≤ f') (hf1 : f' ≤ 1) : power n p₀ fpr f ≤ power n p₀ fpr f' := by
  obtain ⟨hd0, hd1⟩ := randomization_mem (n := n) (p₀ := p₀) hfpr hfpr1
  rw [power_eq_mix hfpr hfpr1, power_eq_mix hfpr hfpr1]
  have a := upperTail_mono (n := n) hf0 hff' hf1 (criticalCount n p₀ fpr)
  have b := upperTail_mono (n := n) hf0 hff' hf1 (criticalCount n p₀ fpr - 1)
  have : 0 ≤ 1 - randomization n p₀ fpr := by linarith
  nlinarith [mul_le_mul_of_nonneg_left a this, mul_le_mul_of_nonneg_left b hd0]

/-- **Power increases with purity** at the ABSOLUTE allelic fraction `α s / (α q + 2 (1 - α))`
of a clonal mutation of multiplicity `0 ≤ s ≤ q` (Carter et al. 2012, Eqs. 2, 9, 10). -/
theorem power_somaticAF_mono_purity {n : ℕ} {p₀ fpr α α' q s : ℝ} (hfpr : 0 ≤ fpr)
    (hfpr1 : fpr < 1) (hα0 : 0 ≤ α) (hαα' : α ≤ α') (hα1 : α' ≤ 1) (hq : 0 < q) (hs : 0 ≤ s)
    (hsq : s ≤ q) : power n p₀ fpr (somaticAF α q s) ≤ power n p₀ fpr (somaticAF α' q s) :=
  power_mono hfpr hfpr1 (somaticAF_nonneg hα0 (hαα'.trans hα1) hq hs)
    (somaticAF_mono_purity hα0 hαα' hα1 hq hs)
    (somaticAF_le_one (hα0.trans hαα') hα1 hq hsq)

/-- **Power decreases with local copy number** at the ABSOLUTE allelic fraction, for a clonal
mutation of multiplicity `0 ≤ s ≤ q ≤ q'` (Carter et al. 2012, Eqs. 2, 9, 10). -/
theorem power_somaticAF_anti_copy {n : ℕ} {p₀ fpr α q q' s : ℝ} (hfpr : 0 ≤ fpr)
    (hfpr1 : fpr < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q) (hqq' : q ≤ q') (hs : 0 ≤ s)
    (hsq : s ≤ q) : power n p₀ fpr (somaticAF α q' s) ≤ power n p₀ fpr (somaticAF α q s) :=
  power_mono hfpr hfpr1 (somaticAF_nonneg hα0 hα1 (hq.trans_le hqq') hs)
    (somaticAF_anti_copy hα0 hα1 hq hqq' hs) (somaticAF_le_one hα0 hα1 hq hsq)

/-- **Power increases with multiplicity** at the ABSOLUTE allelic fraction, for
`0 ≤ s ≤ s' ≤ q` (Carter et al. 2012, Eqs. 2, 9). -/
theorem power_somaticAF_mono_mult {n : ℕ} {p₀ fpr α q s s' : ℝ} (hfpr : 0 ≤ fpr)
    (hfpr1 : fpr < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hs'q : s' ≤ q) : power n p₀ fpr (somaticAF α q s) ≤ power n p₀ fpr (somaticAF α q s') :=
  power_mono hfpr hfpr1 (somaticAF_nonneg hα0 hα1 hq hs) (somaticAF_mono_mult hα0 hα1 hq hss')
    (somaticAF_le_one hα0 hα1 hq hs'q)

end MathlibExt.Biology.CancerGenomics.DetectionPower
