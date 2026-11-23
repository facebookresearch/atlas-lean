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

end

end MetaMathlibExt
