/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

@[expose]
public section

namespace MetaMathlibExt

/-!
# Generating function of the generalized Catalan-Schroeder recurrence

This module proves, with one source typo corrected, the ordinary
generating function of the generalized Catalan-Schroeder recurrence, including
the Riordan-array form acting on the Catalan generating series.
-/

open scoped BigOperators

private theorem generalizedCatalanSchroeder_coeff_square {R : Type} [CommRing R]
    (a : ℕ → R) (ha0 : a 0 = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) ((PowerSeries.mk a - 1) ^ 2) =
      ∑ k ∈ Finset.range n, a (k + 1) * a (n - k) := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_zero_one, ha0, sub_self,
    zero_mul, Nat.add_sub_add_right]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, PowerSeries.coeff_zero_one, ha0, sub_self, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hnk : n - k ≠ 0 := by
    simp only [Finset.mem_range] at hk
    omega
  simp [PowerSeries.coeff_one, hnk]

/-- **Functional equation of the generalized Catalan–Schröder recurrence.** Let $R$ be a
commutative ring, let $s, t, p \in R$, and let $(a_n)_{n \ge 0}$ be a sequence in $R$ with
$a_0 = 1$, $a_1 = p$ and

$$a_n = s\,a_{n-1} + t \sum_{k=0}^{n-3} a_{k+1}\,a_{n-k-2} \qquad (n \ge 2).$$

Then the power series $A = \sum_{n \ge 0} a_n X^n$ over $R$ satisfies
$A - 1 = pX + sX\,(A - 1) + tX\,(A - 1)^2$. -/
public theorem generalizedCatalanSchroeder_recurrence_functionalEquation
    (R : Type) [CommRing R] (s t p : R) (a : ℕ → R) (ha0 : a 0 = 1) (ha1 : a 1 = p)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      a n = s * a (n - 1) +
        t * Finset.sum (Finset.range (n - 2)) (fun k => a (k + 1) * a (n - k - 2))) :
    PowerSeries.mk a - 1 =
      PowerSeries.C p * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X * (PowerSeries.mk a - 1) +
          PowerSeries.C t * PowerSeries.X * (PowerSeries.mk a - 1) ^ 2 := by
  have hleft : PowerSeries.mk a - 1 =
      PowerSeries.X * PowerSeries.C p +
        PowerSeries.X * (PowerSeries.C s * (PowerSeries.mk a - 1)) +
          PowerSeries.X * (PowerSeries.C t * (PowerSeries.mk a - 1) ^ 2) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [ha0]
    | succ n =>
      cases n with
      | zero => simp [ha0, ha1]
      | succ n =>
        simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one,
          Nat.succ_ne_zero, ↓reduceIte, sub_zero, map_add, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_C, PowerSeries.coeff_C_mul]
        rw [generalizedCatalanSchroeder_coeff_square a ha0 n]
        have hsum :
            (∑ k ∈ Finset.range n, a (k + 1) * a (n - k)) =
              ∑ k ∈ Finset.range (n + 2 - 2), a (k + 1) * a (n + 2 - k - 2) := by
          apply Finset.sum_congr
          · congr 1
          · intro k hk
            congr 2
            simp only [Finset.mem_range] at hk
            omega
        rw [hsum]
        have hn2 : n + 1 + 1 = n + 2 := by omega
        have hn1 : n + 2 - 1 = n + 1 := by omega
        simpa only [Nat.succ_eq_add_one, zero_add, hn2, hn1] using
          hrec (n + 2) (by omega)
  calc
    PowerSeries.mk a - 1 = _ := hleft
    _ = PowerSeries.C p * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X * (PowerSeries.mk a - 1) +
            PowerSeries.C t * PowerSeries.X * (PowerSeries.mk a - 1) ^ 2 := by
      ring

private theorem generalizedCatalanSchroeder_catalan_equation
    (R : Type) [CommRing R] :
    PowerSeries.mk (fun n => (catalan n : R)) =
      1 + PowerSeries.X * PowerSeries.mk (fun n => (catalan n : R)) ^ 2 := by
  let castHom : ℕ →+* R := Nat.castRingHom R
  have hmap : PowerSeries.map castHom PowerSeries.catalanSeries =
      PowerSeries.mk (fun n => (catalan n : R)) := by
    apply PowerSeries.ext
    intro n
    simp [castHom]
  have h := congrArg (PowerSeries.map castHom)
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, hmap] at h
  calc
    PowerSeries.mk (fun n => (catalan n : R)) =
        PowerSeries.mk (fun n => (catalan n : R)) ^ 2 * PowerSeries.X + 1 := h.symm
    _ = 1 + PowerSeries.X * PowerSeries.mk (fun n => (catalan n : R)) ^ 2 := by ring

private theorem generalizedCatalanSchroeder_constantCoeff_f
    {R : Type} [CommRing R] (s t p : R) (f : PowerSeries R)
    (hf : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 * f =
      PowerSeries.C t * PowerSeries.X *
        (1 + PowerSeries.C (p - s + t) * PowerSeries.X)) :
    PowerSeries.constantCoeff f = 0 := by
  have h := congrArg (PowerSeries.constantCoeff (R := R)) hf
  simpa using h

private theorem generalizedCatalanSchroeder_subst_catalan_equation
    {R : Type} [CommRing R] (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.mk (fun n => (catalan n : R))) =
      1 + f * PowerSeries.subst f (PowerSeries.mk (fun n => (catalan n : R))) ^ 2 := by
  have hs : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  rw [← PowerSeries.coe_substAlgHom hs]
  simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X] using
    congrArg (PowerSeries.substAlgHom hs)
      (generalizedCatalanSchroeder_catalan_equation R)

private theorem generalizedCatalanSchroeder_key_identity
    {R : Type} [CommRing R] (s t p : R) (g f y : PowerSeries R)
    (hg : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) * g =
      1 + PowerSeries.C (p - s + t) * PowerSeries.X)
    (hf : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 * f =
      PowerSeries.C t * PowerSeries.X *
        (1 + PowerSeries.C (p - s + t) * PowerSeries.X))
    (hy : y = 1 + f * y ^ 2) :
    PowerSeries.C t * PowerSeries.X * (g * y) ^ 2 =
      (1 + PowerSeries.C (p - s + t) * PowerSeries.X) * (y - 1) := by
  have hy' : y - 1 = f * y ^ 2 := by
    linear_combination hy
  have hu : IsUnit (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  apply (hu.pow 2).mul_left_cancel
  calc
    (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 *
          (PowerSeries.C t * PowerSeries.X * (g * y) ^ 2) =
        PowerSeries.C t * PowerSeries.X *
          ((1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) * g) ^ 2 * y ^ 2 := by
      ring
    _ = PowerSeries.C t * PowerSeries.X *
          (1 + PowerSeries.C (p - s + t) * PowerSeries.X) ^ 2 * y ^ 2 := by
      rw [hg]
    _ = (1 + PowerSeries.C (p - s + t) * PowerSeries.X) *
          ((1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 * f) * y ^ 2 := by
      rw [hf]
      ring
    _ = (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 *
          ((1 + PowerSeries.C (p - s + t) * PowerSeries.X) * (y - 1)) := by
      rw [hy']
      ring

private theorem generalizedCatalanSchroeder_candidate_functionalEquation
    {R : Type} [CommRing R] (s t p : R) (g y : PowerSeries R)
    (hg : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) * g =
      1 + PowerSeries.C (p - s + t) * PowerSeries.X)
    (hkey : PowerSeries.C t * PowerSeries.X * (g * y) ^ 2 =
      (1 + PowerSeries.C (p - s + t) * PowerSeries.X) * (y - 1)) :
    g * y - 1 =
      PowerSeries.C p * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X * (g * y - 1) +
          PowerSeries.C t * PowerSeries.X * (g * y - 1) ^ 2 := by
  simp only [map_sub, map_add, map_mul, map_ofNat] at hg hkey ⊢
  linear_combination y * hg - hkey

private theorem generalizedCatalanSchroeder_coeff_square_eq
    {R : Type} [CommRing R] {B B' : PowerSeries R} (n : ℕ)
    (h : ∀ k, k ≤ n → PowerSeries.coeff k B = PowerSeries.coeff k B') :
    PowerSeries.coeff n (B ^ 2) = PowerSeries.coeff n (B' ^ 2) := by
  rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h ij.1 (by omega), h ij.2 (by omega)]

private theorem generalizedCatalanSchroeder_functionalEquation_unique
    {R : Type} [CommRing R] (s t p : R) (B B' : PowerSeries R)
    (hB : B = PowerSeries.C p * PowerSeries.X +
      PowerSeries.C s * PowerSeries.X * B + PowerSeries.C t * PowerSeries.X * B ^ 2)
    (hB' : B' = PowerSeries.C p * PowerSeries.X +
      PowerSeries.C s * PowerSeries.X * B' + PowerSeries.C t * PowerSeries.X * B' ^ 2) :
    B = B' := by
  have hBleft : B =
      PowerSeries.X * PowerSeries.C p + PowerSeries.X * (PowerSeries.C s * B) +
        PowerSeries.X * (PowerSeries.C t * B ^ 2) := calc
    B = PowerSeries.C p * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X * B +
          PowerSeries.C t * PowerSeries.X * B ^ 2 := hB
    _ = _ := by ring
  have hBleft' : B' =
      PowerSeries.X * PowerSeries.C p + PowerSeries.X * (PowerSeries.C s * B') +
        PowerSeries.X * (PowerSeries.C t * B' ^ 2) := calc
    B' = PowerSeries.C p * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X * B' +
          PowerSeries.C t * PowerSeries.X * B' ^ 2 := hB'
    _ = _ := by ring
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      have eB : PowerSeries.coeff 0 B = 0 := by
        simpa using congrArg (PowerSeries.coeff 0) hBleft
      have eB' : PowerSeries.coeff 0 B' = 0 := by
        simpa using congrArg (PowerSeries.coeff 0) hBleft'
      rw [eB, eB']
    | succ n =>
      have eB : PowerSeries.coeff (n + 1) B =
          (if n = 0 then p else 0) + s * PowerSeries.coeff n B +
            t * PowerSeries.coeff n (B ^ 2) := by
        simpa only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C,
          PowerSeries.coeff_C_mul] using
            congrArg (PowerSeries.coeff (n + 1)) hBleft
      have eB' : PowerSeries.coeff (n + 1) B' =
          (if n = 0 then p else 0) + s * PowerSeries.coeff n B' +
            t * PowerSeries.coeff n (B' ^ 2) := by
        simpa only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C,
          PowerSeries.coeff_C_mul] using
            congrArg (PowerSeries.coeff (n + 1)) hBleft'
      have hprev : PowerSeries.coeff n B = PowerSeries.coeff n B' :=
        ih n (by omega)
      have hsq : PowerSeries.coeff n (B ^ 2) = PowerSeries.coeff n (B' ^ 2) :=
        generalizedCatalanSchroeder_coeff_square_eq n fun k hk => ih k (by omega)
      rw [eB, eB', hprev, hsq]

/--
**Generating function of the generalized Catalan–Schröder numbers.** Let $R$ be a commutative
ring, let $s, t, p \in R$, and let $(a_n)_{n \ge 0}$ be a sequence in $R$ with $a_0 = 1$,
$a_1 = p$ and

$$a_n = s\,a_{n-1} + t \sum_{k=0}^{n-3} a_{k+1}\,a_{n-k-2} \qquad (n \ge 2).$$

Let $g$ and $f$ be formal power series over $R$ with

$$(1 - (s - 2t)X)\,g = 1 + (p - s + t)X, \qquad (1 - (s - 2t)X)^2 f = tX\,(1 + (p - s + t)X),$$

and let $C(X) = \sum_{n \ge 0} C_n X^n$, where $C_n$ is the $n$-th Catalan number viewed in $R$.
Then $\sum_{n \ge 0} a_n X^n = g \cdot C(f)$, where $C(f)$ is the power series obtained by
substituting $f$ for $X$ in $C$. Since $1 - (s - 2t)X$ is invertible in $R[[X]]$, these
equations determine $g$ and $f$, and $f$ has zero constant term.

Barry prints $f$ without the factor $X$ in $1 + (p - s + t)X$. That version is false: for
$s = 2$, $t = 1$, $p = 2$ the resulting series $g \cdot C(f)$ has coefficient $3$ at $X$, not
$a_1 = 2$. The recurrence forces the factor restored here.

The proof substitutes $f$ into the Catalan equation $C = 1 + X C^2$, shows that $g \cdot C(f)$
satisfies the same quadratic functional equation as $\sum_{n \ge 0} a_n X^n$, and concludes by
comparing coefficients.

Proves `Wanted` entry `generalizedCatalanSchroeder_generatingFunction`.

Source: Paul Barry, "Generalized Catalan Recurrences, Riordan Arrays, Elliptic Curves, and
Orthogonal Polynomials", Journal of Integer Sequences 24 (2021), Article 21.5.1, Proposition lines
367-373, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry/barry431.tex>.
-/
public theorem generalizedCatalanSchroeder_generatingFunction (R : Type) [CommRing R]
    (s : R) (t : R) (p : R) (a : ℕ → R) (ha0 : a 0 = 1) (ha1 : a 1 = p)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      a n = s * a (n - 1) +
        t * Finset.sum (Finset.range (n - 2)) (fun k => a (k + 1) * a (n - k - 2)))
    (g : PowerSeries R)
    (hg : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) * g =
      1 + PowerSeries.C (p - s + t) * PowerSeries.X)
    (f : PowerSeries R)
    (hf : (1 - PowerSeries.C (s - 2 * t) * PowerSeries.X) ^ 2 * f =
      PowerSeries.C t * PowerSeries.X * (1 + PowerSeries.C (p - s + t) * PowerSeries.X)) :
    PowerSeries.mk a = g * PowerSeries.subst f (PowerSeries.mk (fun n => (catalan n : R))) := by
  let y := PowerSeries.subst f (PowerSeries.mk (fun n => (catalan n : R)))
  have hA := generalizedCatalanSchroeder_recurrence_functionalEquation
    R s t p a ha0 ha1 hrec
  have hf0 : PowerSeries.constantCoeff f = 0 :=
    generalizedCatalanSchroeder_constantCoeff_f s t p f hf
  have hy : y = 1 + f * y ^ 2 := by
    exact generalizedCatalanSchroeder_subst_catalan_equation f hf0
  have hkey : PowerSeries.C t * PowerSeries.X * (g * y) ^ 2 =
      (1 + PowerSeries.C (p - s + t) * PowerSeries.X) * (y - 1) :=
    generalizedCatalanSchroeder_key_identity s t p g f y hg hf hy
  have hG : g * y - 1 =
      PowerSeries.C p * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X * (g * y - 1) +
          PowerSeries.C t * PowerSeries.X * (g * y - 1) ^ 2 :=
    generalizedCatalanSchroeder_candidate_functionalEquation s t p g y hg hkey
  have hsame : PowerSeries.mk a - 1 = g * y - 1 :=
    generalizedCatalanSchroeder_functionalEquation_unique
      s t p (PowerSeries.mk a - 1) (g * y - 1) hA hG
  change PowerSeries.mk a = g * y
  linear_combination hsame

end MetaMathlibExt
