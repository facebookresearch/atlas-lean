/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum

/-!
# Carlitz-type sequences

For real `q`, a sequence of functions `T_n : ℝ → ℝ` is Carlitz-type with associated real sequence
`(a_k)` when `T_n(x) = (q - 1)⁻ⁿ ∑_{k=0}^{n} (-1)^{n-k} C(n,k) a_k q^{kx}` for every natural `n`
and every real `x` (`MetaMathlibExt.IsCarlitzTypeWith`). Carlitz's `q`-polynomials `η_n(x)` and
`q`-Bernoulli polynomials `β_n(x)` are of this form.

## Main statements

* `MetaMathlibExt.IsCarlitzTypeWith.apply_zero`: `T_0(x) = a_0`.
* `MetaMathlibExt.isCarlitzTypeWith_closure`: for real `q > 0` with `q ≠ 1`, the class of
  Carlitz-type sequences is closed under four operations: `n q^x T_{n-1}(x)`,
  `q^{-x} T_{n+1}(x)/(n + 1)` (when `a_0 = 0`), `q^{-x} (T_n(x) + (q - 1) T_{n+1}(x))` and
  `n (T_{n-1}(x) + (q - 1) T_n(x))` are Carlitz-type, with explicit associated sequences.
* `MetaMathlibExt.sum_qpow_mul_qBracket_pow` expresses the sum of `q^(rk) [k]^n` as a weighted
  difference of values of a Carlitz-type sequence.
* `MetaMathlibExt.sum_qpow_mul_qBracket_pow_eq_carlitzEta` evaluates the finite sum of
  `q^k [k]^{n-1}` as the difference of two values of the Carlitz polynomial divided by `n`.
* `MetaMathlibExt.sum_qpow_mul_qBracket_pow_eq_carlitzBeta` evaluates two weighted sums using
  the Carlitz `q`-Bernoulli polynomials.
* `MetaMathlibExt.sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta` extends this evaluation
  to every natural order of the extended Carlitz polynomials.

## Proof

Each property is a computation with the explicit form of `T_n`. For the first two, shift the
summation index by one (the term `k = 0` vanishes) and use
`(m + 1) C(m, k) = C(m + 1, k + 1) (k + 1)` together with `q^{(k+1)x} = q^{kx} q^x`. For the third,
split `C(n + 1, k)` by Pascal's rule (`Finset.sum_choose_succ_mul`): the part with `C(n, k)` cancels
`T_n(x)`, so `T_n(x) + (q - 1) T_{n+1}(x) = (q - 1)⁻ⁿ ∑_{k=0}^{n} (-1)^{n-k} C(n,k) a_{k+1}
q^{(k+1)x}`, and multiplying by `q^{-x}` gives the claim. The fourth is the first applied to the
sequence of the third, as in the source.

## References

* Bakir Farhi, *q-analogues of sums of consecutive powers of natural numbers and extended Carlitz
  q-Bernoulli numbers and polynomials*, arXiv:2501.02499v1 (2025), Definition 2.1 and
  Proposition 2.11. The declaration docstrings cite the journal version, INTEGERS 26 (2026),
  Article A85.
-/

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- **Carlitz-type sequences.** For real $q$, a sequence of functions
$T_n : \mathbb{R} \to \mathbb{R}$, $n \ge 0$, is Carlitz-type with associated real sequence
$(a_k)_{k \ge 0}$ if for every natural number $n$ and every real $x$,
$T_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public def IsCarlitzTypeWith (q : ℝ) (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n x, T n x = ((q - 1) ^ n)⁻¹ *
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x)

/-- **The zeroth term of a Carlitz-type sequence.** Let $q$ be a real number. If $(T_n)$ is a
Carlitz-type $q$-polynomial sequence with associated real sequence $(a_k)$, then $T_0(x) = a_0$
for every real $x$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public theorem IsCarlitzTypeWith.apply_zero {q : ℝ} {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (h : IsCarlitzTypeWith q T a) (x : ℝ) : T 0 x = a 0 := by
  simp [h 0 x]

namespace IsCarlitzTypeWith

variable {q : ℝ} {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}

/-- For `q > 0`, `q^{(k+1)x} = q^{kx} q^x`. -/
private theorem rpow_natCast_succ_mul (hq0 : 0 < q) (k : ℕ) (x : ℝ) :
    q ^ (((k + 1 : ℕ) : ℝ) * x) = q ^ ((k : ℝ) * x) * q ^ x := by
  rw [Nat.cast_succ, add_mul, one_mul, Real.rpow_add hq0]

/-- The absorption identity `C(m + 1, k + 1) (k + 1) = (m + 1) C(m, k)`, cast to `ℝ`. -/
private theorem choose_succ_mul_succ (m k : ℕ) :
    ((m + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) := by
  exact_mod_cast (Nat.add_one_mul_choose_eq m k).symm

/-- Property (i): `n q^x T_{n-1}(x)` is Carlitz-type with associated sequence
`(q - 1) k a_{k-1}`. -/
private theorem qpow_mul_pred (hq0 : 0 < q) (hq : q - 1 ≠ 0) (h : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => q ^ x * n * T (n - 1) x)
      (fun k => (q - 1) * k * a (k - 1)) := by
  intro n x
  cases n with
  | zero => simp
  | succ m =>
    have hterm : ∀ k ∈ range (m + 1),
        (-1 : ℝ) ^ (m + 1 - (k + 1)) * ((m + 1).choose (k + 1) : ℝ) *
            ((q - 1) * ((k + 1 : ℕ) : ℝ) * a (k + 1 - 1)) * q ^ (((k + 1 : ℕ) : ℝ) * x) =
          ((q - 1) * ((m + 1 : ℕ) : ℝ) * q ^ x) *
            ((-1 : ℝ) ^ (m - k) * (m.choose k : ℝ) * a k * q ^ ((k : ℝ) * x)) := by
      intro k _
      rw [Nat.add_sub_add_right, Nat.add_sub_cancel, rpow_natCast_succ_mul hq0]
      linear_combination ((-1 : ℝ) ^ (m - k) * (q - 1) * a k * q ^ ((k : ℝ) * x) * q ^ x) *
        choose_succ_mul_succ m k
    beta_reduce
    rw [Nat.add_sub_cancel, h m x, sum_range_succ' _ (m + 1), sum_congr rfl hterm, ← mul_sum]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    generalize ∑ k ∈ range (m + 1),
      (-1 : ℝ) ^ (m - k) * (m.choose k : ℝ) * a k * q ^ ((k : ℝ) * x) = S
    rw [pow_succ]
    field_simp

/-- Pascal's rule: `T_n(x) + (q - 1) T_{n+1}(x)` is the Carlitz-type sum of order `n` with
`a_{k+1} q^{(k+1)x}` in place of `a_k q^{kx}`. -/
private theorem add_sub_one_mul_succ (hq : q - 1 ≠ 0) (h : IsCarlitzTypeWith q T a) (n : ℕ)
    (x : ℝ) :
    T n x + (q - 1) * T (n + 1) x = ((q - 1) ^ n)⁻¹ *
      ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a (k + 1) *
        q ^ (((k + 1 : ℕ) : ℝ) * x) := by
  have hfirst : ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) * ((-1 : ℝ) ^ (n + 1 - k) * (a k * q ^ ((k : ℝ) * x))) =
        -∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [Nat.sub_add_comm (Nat.lt_succ_iff.mp (mem_range.mp hk)), pow_succ]
    ring
  have hsplit : ∑ k ∈ range (n + 1 + 1),
      (-1 : ℝ) ^ (n + 1 - k) * ((n + 1).choose k : ℝ) * a k * q ^ ((k : ℝ) * x) =
        -∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x) +
          ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a (k + 1) *
            q ^ (((k + 1 : ℕ) : ℝ) * x) := by
    rw [← hfirst]
    calc _ = ∑ k ∈ range (n + 2),
          ((n + 1).choose k : ℝ) * ((-1 : ℝ) ^ (n + 1 - k) * (a k * q ^ ((k : ℝ) * x))) :=
          sum_congr rfl fun k _ => by ring
      _ = _ := sum_choose_succ_mul (fun i j => (-1 : ℝ) ^ j * (a i * q ^ ((i : ℝ) * x))) n
      _ = _ := by
        congr 1
        exact sum_congr rfl fun k _ => by ring
  rw [h n x, h (n + 1) x, hsplit]
  generalize ∑ k ∈ range (n + 1),
    (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x) = S
  generalize ∑ k ∈ range (n + 1),
    (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a (k + 1) * q ^ (((k + 1 : ℕ) : ℝ) * x) = S'
  rw [pow_succ]
  field_simp
  ring

/-- Property (iii): `q^{-x} (T_n(x) + (q - 1) T_{n+1}(x))` is Carlitz-type with associated
sequence `a_{k+1}`. -/
private theorem qpow_neg_mul_add (hq0 : 0 < q) (hq : q - 1 ≠ 0) (h : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => q ^ (-x) * (T n x + (q - 1) * T (n + 1) x))
      (fun k => a (k + 1)) := by
  intro n x
  beta_reduce
  rw [add_sub_one_mul_succ hq h n x, mul_left_comm, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [rpow_natCast_succ_mul hq0, Real.rpow_neg hq0.le]
  field_simp [(Real.rpow_pos_of_pos hq0 x).ne']

/-- Property (ii): if `a_0 = 0`, then `q^{-x} T_{n+1}(x)/(n + 1)` is Carlitz-type with associated
sequence `a_{k+1}/((q - 1)(k + 1))`. -/
private theorem qpow_neg_mul_succ_div (hq0 : 0 < q) (hq : q - 1 ≠ 0)
    (h : IsCarlitzTypeWith q T a) (ha0 : a 0 = 0) :
    IsCarlitzTypeWith q (fun n x => q ^ (-x) * T (n + 1) x / (n + 1))
      (fun k => a (k + 1) / ((q - 1) * (k + 1))) := by
  intro n x
  have hterm : ∀ k ∈ range (n + 1),
      (-1 : ℝ) ^ (n + 1 - (k + 1)) * ((n + 1).choose (k + 1) : ℝ) * a (k + 1) *
          q ^ (((k + 1 : ℕ) : ℝ) * x) =
        ((q - 1) * ((n : ℝ) + 1) * q ^ x) *
          ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * (a (k + 1) / ((q - 1) * ((k : ℝ) + 1))) *
            q ^ ((k : ℝ) * x)) := by
    intro k _
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hc : ((n + 1).choose (k + 1) : ℝ) = ((n : ℝ) + 1) * (n.choose k : ℝ) / ((k : ℝ) + 1) := by
      rw [eq_div_iff hk]
      exact_mod_cast choose_succ_mul_succ n k
    rw [Nat.add_sub_add_right, rpow_natCast_succ_mul hq0, hc]
    field_simp
  beta_reduce
  rw [h (n + 1) x, sum_range_succ' _ (n + 1), sum_congr rfl hterm, ← mul_sum]
  simp only [ha0, mul_zero, zero_mul, add_zero]
  generalize ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (a (k + 1) / ((q - 1) * ((k : ℝ) + 1))) * q ^ ((k : ℝ) * x) = S
  rw [pow_succ, Real.rpow_neg hq0.le]
  field_simp [(Real.rpow_pos_of_pos hq0 x).ne']

/-- Property (iv): `n (T_{n-1}(x) + (q - 1) T_n(x))` is Carlitz-type with associated sequence
`(q - 1) k a_k`; it is property (i) applied to the sequence of property (iii). -/
private theorem mul_pred_add (hq0 : 0 < q) (hq : q - 1 ≠ 0) (h : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => n * (T (n - 1) x + (q - 1) * T n x))
      (fun k => (q - 1) * k * a k) := by
  have h' := qpow_mul_pred hq0 hq (qpow_neg_mul_add hq0 hq h)
  intro n x
  cases n with
  | zero => simp
  | succ m =>
    have hm := h' (m + 1) x
    have hcoeff : ∀ k ∈ range (m + 1 + 1),
        (-1 : ℝ) ^ (m + 1 - k) * ((m + 1).choose k : ℝ) * ((q - 1) * k * a (k - 1 + 1)) *
            q ^ ((k : ℝ) * x) =
          (-1 : ℝ) ^ (m + 1 - k) * ((m + 1).choose k : ℝ) * ((q - 1) * k * a k) *
            q ^ ((k : ℝ) * x) := by
      intro k _
      cases k with
      | zero => simp
      | succ j => rw [Nat.add_sub_cancel]
    beta_reduce at hm ⊢
    rw [Nat.add_sub_cancel, sum_congr rfl hcoeff, Real.rpow_neg hq0.le] at hm
    rw [Nat.add_sub_cancel, ← hm]
    field_simp [(Real.rpow_pos_of_pos hq0 x).ne']

end IsCarlitzTypeWith

/-- **Closure properties of Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$ be real, and let
$(T_n)$ be a Carlitz-type sequence of functions $\mathbb{R} \to \mathbb{R}$ with associated real
sequence $(a_k)$. Then:
(i) $n q^x T_{n-1}(x)$ is Carlitz-type with associated sequence $(q - 1) k a_{k-1}$;
(ii) if $a_0 = 0$, then $q^{-x} T_{n+1}(x)/(n + 1)$ is Carlitz-type with associated sequence
$a_{k+1}/((q - 1)(k + 1))$;
(iii) $q^{-x} (T_n(x) + (q - 1) T_{n+1}(x))$ is Carlitz-type with associated sequence $a_{k+1}$;
(iv) $n (T_{n-1}(x) + (q - 1) T_n(x))$ is Carlitz-type with associated sequence $(q - 1) k a_k$.
At $n = 0$ the functions in (i) and (iv) are $0$, and at $k = 0$ the associated sequence in (i)
is $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.6
(`integers-2026-A85-prop-2-6`). -/
public theorem isCarlitzTypeWith_closure (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) (hT : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => q ^ x * n * T (n - 1) x)
        (fun k => (q - 1) * k * a (k - 1)) ∧
      (a 0 = 0 → IsCarlitzTypeWith q (fun n x => q ^ (-x) * T (n + 1) x / (n + 1))
        (fun k => a (k + 1) / ((q - 1) * (k + 1)))) ∧
      IsCarlitzTypeWith q (fun n x => q ^ (-x) * (T n x + (q - 1) * T (n + 1) x))
        (fun k => a (k + 1)) ∧
      IsCarlitzTypeWith q (fun n x => n * (T (n - 1) x + (q - 1) * T n x))
        (fun k => (q - 1) * k * a k) := by
  have hq : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  exact ⟨hT.qpow_mul_pred hq0 hq, hT.qpow_neg_mul_succ_div hq0 hq, hT.qpow_neg_mul_add hq0 hq,
    hT.mul_pred_add hq0 hq⟩

/-- **The $q$-analogue of a real number.** For real numbers $q$ and $x$, the $q$-analogue of $x$
is
$$[x]_q = \frac{q^x - 1}{q - 1},$$
where $q^x$ is the real power; we write $[x]$ when $q$ is fixed. When $q = 1$ the denominator is
$0$ and the quotient is taken to be $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public noncomputable def qBracket (q x : ℝ) : ℝ :=
  (q ^ x - 1) / (q - 1)

/-- **The $q$-analogue of $0$ is $0$.** For every real number $q$, $[0]_q = 0$, where
$[x]_q = (q^x - 1)/(q - 1)$ is the $q$-analogue of a real number $x$, taken to be $0$ when
$q = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_zero (q : ℝ) : qBracket q 0 = 0 := by
  simp [qBracket]

/-- **The $q$-number of $1$.** For real $q \ne 1$, the $q$-analogue $[x] = (q^x - 1)/(q - 1)$
satisfies $[1] = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_one {q : ℝ} (hq : q ≠ 1) : qBracket q 1 = 1 := by
  rw [qBracket, Real.rpow_one, div_self (sub_ne_zero.mpr hq)]

/-- For real $q > 0$, the powers $[x]_q^n$ of the $q$-analogue $[x]_q = (q^x-1)/(q-1)$
form a Carlitz-type sequence with constant associated sequence $1$, by the binomial theorem
for $(q^x-1)^n$. At $q=1$ the quotient defining $[x]_q$ is taken to be zero. -/
public theorem qBracket.isCarlitzTypeWith_pow {q : ℝ} (hq0 : 0 < q) :
    IsCarlitzTypeWith q (fun n x => qBracket q x ^ n) fun _ => 1 := by
  intro n x
  beta_reduce
  rw [qBracket, div_pow, div_eq_inv_mul, sub_eq_add_neg (q ^ x) 1, add_pow (q ^ x) (-1) n]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [mul_comm (k : ℝ) x, Real.rpow_mul_natCast hq0.le]
  ring

/-- **Sums of $q^{rk} [k]^n$ via Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and let $r \ge 1$ be a natural number. Let $S_m(x)$
($m \in \mathbb{N}$, $x \in \mathbb{R}$) be the Carlitz-type sequence with associated sequence
$a_k = 1/((q - 1)[k + r])$, that is,
$$S_m(x) = (q - 1)^{-m} \sum_{k=0}^{m} (-1)^{m-k} \binom{m}{k} a_k q^{kx}$$
for all $m$ and all real $x$. Then for all natural numbers $n$ and $N$,
$$\sum_{k=0}^{N-1} q^{rk} [k]^n = q^{rN} S_n(N) - S_n(0),$$
where $0^0 = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.3
(`integers-2026-A85-thm-2-3`). -/
public theorem sum_qpow_mul_qBracket_pow (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r n N : ℕ) (hr : 0 < r) (S : ℕ → ℝ → ℝ)
    (hS : IsCarlitzTypeWith q S fun k => 1 / ((q - 1) * qBracket q ((k + r : ℕ) : ℝ))) :
    ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n = q ^ (r * N) * S n N - S n 0 := by
  have hcoeff (j : ℕ) :
      1 / ((q - 1) * qBracket q ((j + r : ℕ) : ℝ)) * (q ^ j * q ^ r - 1) = 1 := by
    have hpow : q ^ (j + r) ≠ 1 :=
      fun h => hq1 ((pow_eq_one_iff_of_nonneg hq0.le (by omega)).mp h)
    rw [qBracket, Real.rpow_natCast, ← pow_add]
    field_simp [sub_ne_zero.mpr hq1, sub_ne_zero.mpr hpow]
  -- The weighted forward difference cancels the denominator of each Carlitz coefficient.
  have hdiff (x : ℝ) : q ^ r * S n (x + 1) - S n x = qBracket q x ^ n := by
    refine Eq.trans ?_ (qBracket.isCarlitzTypeWith_pow hq0 n x).symm
    rw [hS n (x + 1), hS n x, mul_left_comm (q ^ r), ← mul_sub, mul_sum,
      ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    simp only [mul_add, mul_one, Real.rpow_add hq0, Real.rpow_natCast]
    linear_combination ((-1 : ℝ) ^ (n - j) * (n.choose j : ℝ) * q ^ ((j : ℝ) * x)) * hcoeff j
  calc
    _ = ∑ k ∈ range N, (q ^ (r * (k + 1)) * S n (k + 1 : ℕ) - q ^ (r * k) * S n k) := by
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.cast_succ, ← hdiff, Nat.mul_succ, pow_add]
      ring
    _ = _ := by simpa using sum_range_sub (fun k : ℕ => q ^ (r * k) * S n k) N

/-- **Carlitz $q$-polynomials $\eta_n$.** For real $q$, write $[y] = (q^y - 1)/(q - 1)$ and let
$a_0 = 1$ and $a_k = k/[k]$ for $k \ge 1$. For natural $n$ and real $x$, Carlitz's $q$-polynomial
is $\eta_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$; that is,
$(\eta_n)$ is the Carlitz-type sequence with associated sequence $(a_k)$. Its values at $0$ are
written $\eta_n = \eta_n(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzEtaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (if k = 0 then 1 else (k : ℝ) / qBracket q k) * q ^ ((k : ℝ) * x)

/-- **The zeroth Carlitz $q$-polynomial.** For all real $q$ and $x$, Carlitz's $q$-polynomial
$\eta_0(x)$ equals $1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzEtaPoly_zero (q x : ℝ) : carlitzEtaPoly q 0 x = 1 := by
  simp [carlitzEtaPoly]

/-- **Carlitz's initial value $\eta_1 = 0$.** For real $q \ne 1$, the value $\eta_1 = \eta_1(0)$ of
Carlitz's $q$-polynomial $\eta_1$ at $0$ equals $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Sections 1
and 2.1. -/
public theorem carlitzEtaPoly_one_zero {q : ℝ} (hq : q ≠ 1) : carlitzEtaPoly q 1 0 = 0 := by
  simp [carlitzEtaPoly, Finset.sum_range_succ, qBracket_one hq]

/-- **Sums of $q^k [k]^{n-1}$ via Carlitz's $q$-polynomials $\eta_n$.** Let $q > 0$ with $q \ne 1$,
let $[x] = (q^x - 1)/(q - 1)$, and let $\eta_n(x)$ be Carlitz's $q$-polynomials, with
$\eta_n = \eta_n(0)$. Then for every natural number $n \ge 1$ and every natural number $N$,
$$\sum_{k=0}^{N-1} q^k [k]^{n-1} = \frac{\eta_n(N) - \eta_n}{n},$$
where $0^0 = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.7
(`integers-2026-A85-cor-2-7`). -/
public theorem sum_qpow_mul_qBracket_pow_eq_carlitzEta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) (hn : 0 < n) :
    ∑ k ∈ range N, q ^ k * qBracket q k ^ (n - 1) =
      (carlitzEtaPoly q n N - carlitzEtaPoly q n 0) / n := by
  have hcoeff (k : ℕ) :
      (if k = 0 then 1 else (k : ℝ) / qBracket q k) * (q ^ k - 1) = (q - 1) * k := by
    by_cases hk : k = 0
    · simp [hk]
    · have hpow : q ^ k - 1 ≠ 0 :=
        sub_ne_zero.mpr (fun h => hq1 ((pow_eq_one_iff_of_nonneg hq0.le hk).mp h))
      rw [ite_eq_right hk, qBracket, Real.rpow_natCast]
      field_simp [hpow, sub_ne_zero.mpr hq1]
  -- Taking a forward difference multiplies the kth coefficient by q^k - 1.
  have hdiff (x : ℝ) : carlitzEtaPoly q n (x + 1) - carlitzEtaPoly q n x =
      q ^ x * n * qBracket q x ^ (n - 1) := by
    have h := (isCarlitzTypeWith_closure q hq0 hq1 _ _ (qBracket.isCarlitzTypeWith_pow hq0)).1 n x
    simp only [mul_one] at h
    rw [h, carlitzEtaPoly, carlitzEtaPoly, ← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, mul_one, Real.rpow_add hq0, Real.rpow_natCast]
    linear_combination
      ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * q ^ ((k : ℝ) * x)) * hcoeff k
  rw [eq_div_iff (Nat.cast_ne_zero.mpr hn.ne'), sum_mul]
  calc
    _ = ∑ k ∈ range N, (carlitzEtaPoly q n (k + 1 : ℕ) - carlitzEtaPoly q n k) := by
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.cast_succ, hdiff, Real.rpow_natCast]
      ring
    _ = _ := by simpa using sum_range_sub (fun k : ℕ => carlitzEtaPoly q n k) N

/-- **Carlitz $q$-Bernoulli polynomials.** For real $q$, write $[y] = (q^y - 1)/(q - 1)$. For
natural $n$ and real $x$, Carlitz's $q$-Bernoulli polynomial is
$\beta_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} \frac{k + 1}{[k + 1]} q^{kx}$;
that is, $(\beta_n)$ is the Carlitz-type sequence with associated sequence
$a_k = (k + 1)/[k + 1]$. The Carlitz $q$-Bernoulli numbers are $\beta_n = \beta_n(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzBetaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (((k : ℝ) + 1) / qBracket q ((k : ℝ) + 1)) * q ^ ((k : ℝ) * x)

/-- **The zeroth Carlitz $q$-Bernoulli polynomial.** For real $q \ne 1$ and every real $x$, the
Carlitz $q$-Bernoulli polynomial $\beta_0(x)$ equals $1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzBetaPoly_zero {q : ℝ} (hq : q ≠ 1) (x : ℝ) : carlitzBetaPoly q 0 x = 1 := by
  simp [carlitzBetaPoly, qBracket_one hq]

/-- **Weighted $q$-power sums via Carlitz's $q$-Bernoulli polynomials.** Let $q > 0$ with
$q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, and let $\beta_n(x)$ be Carlitz's $q$-Bernoulli
polynomials, with $\beta_n = \beta_n(0)$. Then for all natural numbers $n$ and $N$,
$$n \sum_{k=0}^{N-1} q^{2k} [k]^{n-1} + (q - 1) \sum_{k=0}^{N-1} q^k [k]^n =
q^N \beta_n(N) - \beta_n,$$
where $0^0 = 1$, and the first term is $0$ when $n = 0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.8
(`integers-2026-A85-cor-2-8`). -/
public theorem sum_qpow_mul_qBracket_pow_eq_carlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) :
    n * ∑ k ∈ range N, q ^ (2 * k) * qBracket q k ^ (n - 1) +
        (q - 1) * ∑ k ∈ range N, q ^ k * qBracket q k ^ n =
      q ^ N * carlitzBetaPoly q n N - carlitzBetaPoly q n 0 := by
  have hcoeff (j : ℕ) :
      (((j : ℝ) + 1) / qBracket q ((j : ℝ) + 1)) * (q ^ j * q - 1) =
        (q - 1) * (j + 1) := by
    have hpow : q ^ (j + 1) ≠ 1 :=
      fun h => hq1 ((pow_eq_one_iff_of_nonneg hq0.le (Nat.succ_ne_zero j)).mp h)
    rw [qBracket, ← Nat.cast_succ, Real.rpow_natCast, ← pow_succ]
    field_simp [sub_ne_zero.mpr hq1, sub_ne_zero.mpr hpow]
  -- The weighted forward difference multiplies coefficient j by q^(j+1) - 1.
  have hdiff (x : ℝ) : q * carlitzBetaPoly q n (x + 1) - carlitzBetaPoly q n x =
      q ^ x * n * qBracket q x ^ (n - 1) + (q - 1) * qBracket q x ^ n := by
    have h := qBracket.isCarlitzTypeWith_pow hq0
    have hpred := (isCarlitzTypeWith_closure q hq0 hq1 _ _ h).1 n x
    have hpow := h n x
    simp only [mul_one] at hpred hpow
    rw [hpred, hpow, carlitzBetaPoly, carlitzBetaPoly]
    rw [mul_left_comm q, ← mul_sub, mul_left_comm (q - 1), ← mul_add]
    congr 1
    rw [mul_sum, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [mul_add, mul_one, Real.rpow_add hq0, Real.rpow_natCast]
    linear_combination
      ((-1 : ℝ) ^ (n - j) * (n.choose j : ℝ) * q ^ ((j : ℝ) * x)) * hcoeff j
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  calc
    _ = ∑ k ∈ range N,
          (q ^ (k + 1) * carlitzBetaPoly q n (k + 1 : ℕ) - q ^ k * carlitzBetaPoly q n k) := by
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.cast_succ, pow_succ, two_mul, pow_add]
      have hk := hdiff k
      rw [Real.rpow_natCast] at hk
      linear_combination -(q ^ k) * hk
    _ = _ := by simpa using sum_range_sub (fun k : ℕ => q ^ k * carlitzBetaPoly q n k) N

/-- **Extended Carlitz $q$-Bernoulli polynomials.** For real $q$, the extended Carlitz
$q$-Bernoulli polynomials $\beta_n^{(r)}(x)$, indexed by natural numbers $r$ and $n$ and evaluated
at real $x$, are defined by recursion on $r$: $\beta_n^{(0)}(x) = \eta_n(x)$ is Carlitz's
$q$-polynomial, and
$\beta_n^{(r+1)}(x) = q^{-x} \bigl(\beta_n^{(r)}(x) + (q - 1) \beta_{n+1}^{(r)}(x)\bigr)$.
The extended Carlitz $q$-Bernoulli numbers are $\beta_n^{(r)} = \beta_n^{(r)}(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2
(definition of the extended family). -/
public noncomputable def extendedCarlitzBetaPoly (q : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, n, x => carlitzEtaPoly q n x
  | r + 1, n, x => q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x)

/-- **Extended Carlitz $q$-Bernoulli polynomials of order zero.** For every real $q$, natural number
$n$ and real $x$, the extended Carlitz $q$-Bernoulli polynomial $\beta_n^{(0)}(x)$ equals Carlitz's
$q$-polynomial $\eta_n(x)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_zero (q : ℝ) (n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q 0 n x = carlitzEtaPoly q n x := by
  simp [extendedCarlitzBetaPoly]

/-- **Recurrence for the extended Carlitz $q$-Bernoulli polynomials.** For every real $q$, natural
numbers $r$ and $n$, and real $x$, the extended Carlitz $q$-Bernoulli polynomials satisfy
$\beta_n^{(r+1)}(x) = q^{-x} \bigl(\beta_n^{(r)}(x) + (q - 1) \beta_{n+1}^{(r)}(x)\bigr)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_succ (q : ℝ) (r n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q (r + 1) n x = q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x) := by
  simp [extendedCarlitzBetaPoly]

/-- **Weighted $q$-power sums via the extended Carlitz $q$-Bernoulli polynomials.** Let $q > 0$
with $q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, and let $\beta_n^{(r)}(x)$ be the extended Carlitz
$q$-Bernoulli polynomials, with $\beta_n^{(r)} = \beta_n^{(r)}(0)$. Then for all natural numbers
$r$, $n$ and $N$,
$$n \sum_{k=0}^{N-1} q^{(r+1)k} [k]^{n-1} + (q - 1) r \sum_{k=0}^{N-1} q^{rk} [k]^n =
q^{rN} \beta_n^{(r)}(N) - \beta_n^{(r)},$$
where $0^0 = 1$, and the first term is $0$ when $n = 0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.10
(`integers-2026-A85-thm-2-10`). -/
public theorem sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (r n N : ℕ) :
    n * ∑ k ∈ range N, q ^ ((r + 1) * k) * qBracket q k ^ (n - 1) +
        (q - 1) * r * ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n =
      q ^ (r * N) * extendedCarlitzBetaPoly q r n N - extendedCarlitzBetaPoly q r n 0 := by
  let S (r m : ℕ) := ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ m
  let D (r n : ℕ) := q ^ (r * N) * extendedCarlitzBetaPoly q r n N -
    extendedCarlitzBetaPoly q r n 0
  -- Multiplying a summand by q^k = 1 + (q - 1) [k] raises its weight by one.
  have hS (r m : ℕ) : S (r + 1) m = S r m + (q - 1) * S r (m + 1) := by
    dsimp [S]
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    have hk : (q - 1) * qBracket q k = q ^ k - 1 := by
      rw [qBracket, Real.rpow_natCast]
      field_simp [sub_ne_zero.mpr hq1]
    rw [Nat.add_mul, one_mul, pow_add, pow_succ]
    linear_combination -(q ^ (r * k) * qBracket q k ^ m) * hk
  have hpred (r n : ℕ) : (n : ℝ) * S (r + 1) (n - 1) =
      n * S r (n - 1) + (q - 1) * n * S r n := by
    cases n with
    | zero => simp
    | succ m => rw [Nat.add_sub_cancel, hS]; ring
  -- The endpoint difference inherits the defining recurrence of the extended family.
  have hD (r n : ℕ) : D (r + 1) n = D r n + (q - 1) * D r (n + 1) := by
    dsimp [D]
    rw [extendedCarlitzBetaPoly_succ, extendedCarlitzBetaPoly_succ, Nat.add_mul, one_mul,
      pow_add, Real.rpow_neg hq0.le, Real.rpow_natCast, neg_zero, Real.rpow_zero, one_mul]
    field_simp [pow_ne_zero N hq0.ne']
    ring
  change n * S (r + 1) (n - 1) + (q - 1) * r * S r n = D r n
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => simp [D, extendedCarlitzBetaPoly_zero, carlitzEtaPoly_zero]
    | succ m =>
      have h := sum_qpow_mul_qBracket_pow_eq_carlitzEta q hq0 hq1 (m + 1) N (by omega)
      simpa [S, D, extendedCarlitzBetaPoly_zero, mul_comm] using
        (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))).mp h
  | succ r ih =>
    rw [hD, ← ih n, ← ih (n + 1), hpred (r + 1) n]
    simp only [Nat.add_sub_cancel, Nat.cast_succ]
    linear_combination (q - 1) * r * hS r n

end

end MetaMathlibExt
