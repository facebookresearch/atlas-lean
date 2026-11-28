/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer
import Mathlib.RingTheory.Polynomial.Chebyshev
import MathlibExt.NumberTheory.LucasLehmerAcceptableSeed

/-!
# Divisibility of Lehmer's companion sequence by a Mersenne prime

Let $n \ge 3$ be odd and let $M_n = 2^n - 1$ be prime. For integers $r,d,q,X,Y,Z$ with
$\gcd(M_n,Y)=1$ and $4qY^2=rX^2-dZ^2$, suppose the Jacobi symbols of $rd$ and $qr$ at $M_n$
are both $-1$. Then $M_n$ divides the Lehmer companion term at index $2^{n-1}$ with parameters
$R=rX^2$ and $Q=qY^2$. The proof uses the seed $R/Q-2$ modulo $M_n$: it identifies the even
companion terms with scaled Chebyshev evaluations and uses doubling to recover the Lucas–Lehmer
iteration.

## References

* E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality Test*,
  Journal of Integer Sequences **28** (2025), Article 25.2.5, pp. 1–26, §2 (recurrence (2) and
  Theorem 6) and §3 (Lemma 7). <https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.pdf>
* D. H. Lehmer, *An Extended Theory of Lucas' Functions*, Annals of Mathematics **31** (1930),
  pp. 419–448, §1 (Lehmer sequences) and Theorem 4.9 (the criterion behind Lemma 5).
* The Lean proof uses `acceptableSeed_of_jacobi` from
  `MathlibExt.NumberTheory.LucasLehmerAcceptableSeed`. The companion sequence and recurrence
  `lehmerV` and `lehmerV_add_four` come from `WantedExt.NumberTheory.LucasLehmerRationalSeedWanted`.
-/

namespace MetaMathlibExt

/-- **Lehmer's companion sequence.** For integers $R$ and $Q$, Lehmer's companion sequence
$\bar V_k(R, Q)$, $k = 0, 1, 2, \ldots$, is the integer sequence with $\bar V_0 = 2$,
$\bar V_1 = 1$, $\bar V_2 = R - 2Q$, $\bar V_3 = R - 3Q$ and
$\bar V_{k+4} = (R - 2Q)\,\bar V_{k+2} - Q^2\,\bar V_k$ for every $k \ge 0$.

With $P = \sqrt R$ and the Lucas sequence $V_k(P, Q)$ given by $V_0 = 2$, $V_1 = P$ and
$V_{k+2} = P V_{k+1} - Q V_k$, for $R \ne 0$ the term $\bar V_k(R, Q)$ equals $V_k(\sqrt R, Q)$
for even $k$ and $V_k(\sqrt R, Q)/\sqrt R$ for odd $k$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2 (definition of `V̄_n` and
recurrence (2)). -/
@[expose] public def lehmerV (R Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | 2 => R - 2 * Q
  | 3 => R - 3 * Q
  | k + 4 => (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k

/-- **Fourth-order recurrence of Lehmer's companion sequence.** For all integers $R$ and $Q$ and
every natural number $k$, Lehmer's companion sequence satisfies
$\bar V_{k+4}(R, Q) = (R - 2Q)\,\bar V_{k+2}(R, Q) - Q^2\,\bar V_k(R, Q)$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2, recurrence (2). -/
public theorem lehmerV_add_four (R Q : ℤ) (k : ℕ) :
    lehmerV R Q (k + 4) = (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k :=
  rfl

open Polynomial.Chebyshev in
private theorem lehmerV_even_eq_chebyshev {m : ℕ} (R Q : ℤ) (s : ZMod m)
    (hs : (Q : ZMod m) * s = (R : ZMod m) - 2 * (Q : ZMod m)) (k : ℕ) :
    (lehmerV R Q (2 * k) : ZMod m) = (Q : ZMod m) ^ k * (C (ZMod m) (k : ℤ)).eval s := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lehmerV]
  | one => simpa [lehmerV] using hs.symm
  | more k ih₀ ih₁ =>
      rw [show 2 * (k + 2) = 2 * k + 4 by omega, lehmerV_add_four]
      push_cast
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, ih₀, ih₁,
        Nat.cast_add, Nat.cast_one, C_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, ← hs]
      ring

open Polynomial.Chebyshev in
private theorem chebyshev_eval_two_pow {K : Type*} [CommRing K] (s : K) (j : ℕ) :
    (C K (2 ^ j)).eval s = (fun x : K => x ^ 2 - 2)^[j] s := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', C_mul, Polynomial.eval_comp, C_two]
      simp [Function.iterate_succ_apply', ih]

/-- **Divisibility of Lehmer's companion sequence by a Mersenne prime, Diophantine form.** Let
$n \ge 3$ be an odd natural number such that $M_n = 2^n - 1$ is prime, and let $r$, $d$, $q$,
$X$, $Y$, $Z$ be integers with $\gcd(M_n, Y) = 1$ and $4qY^2 = rX^2 - dZ^2$. Put $R = rX^2$ and
$Q = qY^2$, and let $\bar V_k(R, Q)$ denote Lehmer's companion sequence. If the Jacobi symbols
$\left(\frac{rd}{M_n}\right)$ and $\left(\frac{qr}{M_n}\right)$ are both $-1$, then $M_n$ divides
$\bar V_{(M_n+1)/2}(R, Q) = \bar V_{2^{n-1}}(R, Q)$.

Here $D = R - 4Q = dZ^2$, and since $M_n$ is prime the Jacobi symbols are Legendre symbols.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 7. -/
public theorem mersenne_dvd_lehmerV_of_diophantine {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hp : (mersenne n).Prime) (r d q X Y Z : ℤ) (hY : Int.gcd (mersenne n) Y = 1)
    (hdio : 4 * q * Y ^ 2 = r * X ^ 2 - d * Z ^ 2)
    (hrd : jacobiSym (r * d) (mersenne n) = -1) (hqr : jacobiSym (q * r) (mersenne n) = -1) :
    (mersenne n : ℤ) ∣ lehmerV (r * X ^ 2) (q * Y ^ 2) (2 ^ (n - 1)) := by
  let m := mersenne n
  let : Fact m.Prime := ⟨hp⟩
  let χ := quadraticChar (ZMod m)
  have hm4 : m % 4 = 3 := mersenne_mod_four (by omega)
  have htwo : (2 : ZMod m) ≠ 0 := by
    change ((2 : ℕ) : ZMod m) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have hchar_four : χ 4 = 1 := by
    rw [show (4 : ZMod m) = 2 ^ 2 by norm_num, quadraticChar_sq_one' htwo]
  have hchar_neg_four : χ (-4) = -1 := by
    have hneg : χ (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr
      (fun h => ZMod.exists_sq_eq_neg_one_iff.mp h hm4)
    rw [neg_eq_neg_one_mul, map_mul, hneg, hchar_four, mul_one]
  have hrd' : χ ((r : ZMod m) * d) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    simpa only [Int.cast_mul] using (legendreSym.eq_neg_one_iff m).mp
      ((jacobiSym.legendreSym.to_jacobiSym m (r * d)).trans hrd)
  have hqr' : χ ((q : ZMod m) * r) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    simpa only [Int.cast_mul] using (legendreSym.eq_neg_one_iff m).mp
      ((jacobiSym.legendreSym.to_jacobiSym m (q * r)).trans hqr)
  have hr : (r : ZMod m) ≠ 0 := by
    intro h
    simp [χ, h] at hqr'
  have hq : (q : ZMod m) ≠ 0 := by
    intro h
    simp [χ, h] at hqr'
  have hdq : χ ((q : ZMod m) * d) = 1 := by
    have hr_sq : χ ((r : ZMod m) ^ 2) = 1 := quadraticChar_sq_one' hr
    calc
      _ = χ (((r : ZMod m) * d) * ((q : ZMod m) * r)) := by
        rw [show ((r : ZMod m) * d) * ((q : ZMod m) * r) =
          (r : ZMod m) ^ 2 * ((q : ZMod m) * d) by ring,
          map_mul χ ((r : ZMod m) ^ 2), hr_sq, one_mul]
      _ = 1 := by rw [map_mul, hrd', hqr']; norm_num
  have hY' : (Y : ZMod m) ≠ 0 := by
    intro hy
    have h := congrArg (fun a : ℤ => (a : ZMod m)) (Int.gcd_eq_gcd_ab (m : ℤ) Y)
    simp [show Int.gcd (m : ℤ) Y = 1 from hY, hy] at h
  let R := r * X ^ 2
  let Q := q * Y ^ 2
  have hQ : (Q : ZMod m) ≠ 0 := by
    simpa [Q] using mul_ne_zero hq (pow_ne_zero 2 hY')
  have hD : (R : ZMod m) - 4 * (Q : ZMod m) = (d : ZMod m) * (Z : ZMod m) ^ 2 := by
    have heq : R - 4 * Q = d * Z ^ 2 := by
      dsimp [R, Q]
      linear_combination -hdio
    simpa using congrArg (fun a : ℤ => (a : ZMod m)) heq
  let s : ZMod m := (R : ZMod m) / Q - 2
  have hs : (Q : ZMod m) * s = (R : ZMod m) - 2 * (Q : ZMod m) := by
    dsimp only [s]
    rw [mul_sub, mul_comm (Q : ZMod m) ((R : ZMod m) / Q), div_mul_cancel₀ _ hQ, mul_comm _ 2]
  -- Multiplying by `q * Q = (q * Y)^2` leaves the quadratic character unchanged.
  have hscaled (t a b : ZMod m) (h : t * (Q : ZMod m) = a * b ^ 2) :
      χ t = χ ((q : ZMod m) * a) * χ (b ^ 2) := by
    have heq : t * ((q : ZMod m) * Y) ^ 2 = ((q : ZMod m) * a) * b ^ 2 := by
      calc
        _ = (q : ZMod m) * (t * (Q : ZMod m)) := by
          simp only [Q, Int.cast_mul, Int.cast_pow]
          ring
        _ = _ := by rw [h]; ring
    have hsq : χ (((q : ZMod m) * Y) ^ 2) = 1 :=
      quadraticChar_sq_one' (mul_ne_zero hq hY')
    simpa only [map_mul, hsq, mul_one] using congrArg χ heq
  have hplus := hscaled (s + 2) (r : ZMod m) (X : ZMod m) (by
    rw [← Int.cast_pow, ← Int.cast_mul]
    change (s + 2) * (Q : ZMod m) = (R : ZMod m)
    linear_combination hs)
  have hminus := hscaled (s - 2) (d : ZMod m) (Z : ZMod m) (by linear_combination hs + hD)
  rw [hqr', neg_one_mul] at hplus
  rw [hdq, one_mul] at hminus
  -- If `X` vanishes, then `s - 2 = -4`, which cannot have the character of a square.
  have hX : (X : ZMod m) ≠ 0 := by
    intro hx
    have hz : s + 2 = 0 := quadraticChar_eq_zero_iff.mp (by simpa [χ, hx] using hplus)
    have heq : s - 2 = -4 := by linear_combination hz
    rw [heq, hchar_neg_four] at hminus
    exact quadraticChar_neg_one_iff_not_isSquare.mp hminus.symm (IsSquare.sq _)
  rw [quadraticChar_sq_one' hX] at hplus
  have hZ : (Z : ZMod m) ≠ 0 := by
    intro hz
    have hz' : s - 2 = 0 := quadraticChar_eq_zero_iff.mp (by simpa [χ, hz] using hminus)
    have heq : s + 2 = 4 := by linear_combination hz'
    rw [heq, hchar_four] at hplus
    norm_num at hplus
  rw [quadraticChar_sq_one' hZ] at hminus
  obtain ⟨s₁, hs₁⟩ := ZMod.intCast_surjective s
  have hseed : jacobiSym (s₁ + 2) m = -1 ∧ jacobiSym (s₁ - 2) m = 1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym m (s₁ + 2),
      ← jacobiSym.legendreSym.to_jacobiSym m (s₁ - 2)]
    constructor
    · apply (legendreSym.eq_neg_one_iff m).mpr
      simpa only [Int.cast_add, Int.cast_ofNat, hs₁] using
        quadraticChar_neg_one_iff_not_isSquare.mp hplus
    · have hs_sub : ((s₁ - 2 : ℤ) : ZMod m) = s - 2 := by simp [hs₁]
      have hne : s - 2 ≠ 0 := by
        intro hz
        have hzero : χ (s - 2) = 0 := quadraticChar_eq_zero_iff.mpr hz
        exact zero_ne_one (hzero.symm.trans hminus)
      apply (legendreSym.eq_one_iff m (a := s₁ - 2) (by rwa [hs_sub])).mpr
      rw [hs_sub]
      exact (quadraticChar_one_iff_isSquare hne).mp hminus
  have hdiv := (acceptableSeed_of_jacobi n hn h3 s₁ hseed).mp hp
  have hcast : Function.Semiconj (fun a : ℤ => (a : ZMod m))
      (fun a => a ^ 2 - 2) (fun a => a ^ 2 - 2) := by
    intro a
    simp
  have hzero : (fun a : ZMod m => a ^ 2 - 2)^[n - 2] s = 0 := by
    rw [← hs₁, ← hcast.iterate_right (n - 2) s₁]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  change (m : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
    show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ'],
    lehmerV_even_eq_chebyshev R Q s hs]
  push_cast
  rw [chebyshev_eval_two_pow, hzero, mul_zero]

end MetaMathlibExt
