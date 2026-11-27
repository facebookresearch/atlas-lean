/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Harmonic.ShiftedChoose

/-!
# Asymptotics of hyperharmonic numbers

The closed form splits a hyperharmonic number into a binomial coefficient and a difference of
harmonic numbers. For fixed order, the shifted binomial coefficient gives the power of the index
and its factorial normalization, and the Euler–Mascheroni limit gives the logarithmic factor.

## References

* John H. Conway and Richard K. Guy, *The Book of Numbers*, Copernicus, New York (1996),
  p. 258 (the closed form).
* Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1,
  pp. 1–16, Lemma 1 (p. 3).
* István Mező and Ayhan Dil, *Hyperharmonic series involving Hurwitz zeta function*,
  Journal of Number Theory 130 (2010), 360–369 (Li's reference for the asymptotic).
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

@[expose] public section

/-- **Hyperharmonic numbers.** The hyperharmonic numbers $h_n^{(r)} \in \mathbb{Q}$ of order $r$
and index $n$, for natural numbers $r$ and $n$, are defined by recursion on $r$:
$h_n^{(0)} = 1/n$ for $n \ge 1$, $h_0^{(0)} = 0$, and
$$h_n^{(r+1)} = \sum_{k=1}^{n} h_k^{(r)}.$$
Thus $h_0^{(r)} = 0$ for every order $r$, and $h_n^{(1)} = 1 + 1/2 + \dots + 1/n$ is the $n$-th
harmonic number $H_n$. This is the definition of Conway and Guy.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public def hyperharmonic : ℕ → ℕ → ℚ
  | 0, n => 1 / n
  | r + 1, n => ∑ k ∈ Icc 1 n, hyperharmonic r k

/-- **Recursion for the hyperharmonic numbers.** For all natural numbers $r$ and $n$, the
hyperharmonic numbers $h_m^{(s)}$ (of order $s$ and index $m$) satisfy
$$h_n^{(r+1)} = \sum_{k=1}^{n} h_k^{(r)}.$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_succ (r n : ℕ) :
    hyperharmonic (r + 1) n = ∑ k ∈ Icc 1 n, hyperharmonic r k := rfl

/-- **Hyperharmonic numbers of order one are the harmonic numbers.** For every natural number $n$,
the hyperharmonic number $h_n^{(1)}$ of order $1$ and index $n$ equals the $n$-th harmonic number
$H_n = \sum_{k=1}^{n} 1/k$ (in particular $h_0^{(1)} = H_0 = 0$).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_one (n : ℕ) : hyperharmonic 1 n = harmonic n := by
  induction n with
  | zero => simp [hyperharmonic]
  | succ n ih =>
    rw [harmonic_succ, ← ih, hyperharmonic, hyperharmonic, Finset.sum_Icc_succ_top (by omega)]
    simp [hyperharmonic]

end

-- Pascal's identity and the harmonic recurrence give the increment of the closed form.
private theorem choose_mul_harmonic_step (m r : ℕ) :
    ((m + 1).choose (r + 1) : ℚ) * (harmonic (m + 1) - harmonic (r + 1)) =
      (m.choose (r + 1) : ℚ) * (harmonic m - harmonic (r + 1)) +
        (m.choose r : ℚ) * (harmonic m - harmonic r) := by
  have hchoose : ((m + 1).choose (r + 1) : ℚ) * (↑(m + 1) : ℚ)⁻¹ =
      (m.choose r : ℚ) * (↑(r + 1) : ℚ)⁻¹ := by
    have h := Nat.add_one_mul_choose_eq m r
    have h' : (↑(m + 1) : ℚ) * (m.choose r : ℚ) =
        ((m + 1).choose (r + 1) : ℚ) * (↑(r + 1) : ℚ) := by exact_mod_cast h
    field_simp
    exact h'.symm
  rw [harmonic_succ m, add_sub_right_comm, mul_add, hchoose, Nat.choose_succ_succ',
    Nat.cast_add, harmonic_succ r]
  ring

private theorem hyperharmonic_succ_eq_choose_mul (r n : ℕ) :
    hyperharmonic (r + 1) n = ((n + r).choose r : ℚ) * (harmonic (n + r) - harmonic r) := by
  induction r generalizing n with
  | zero => simp [hyperharmonic_one]
  | succ r ihr =>
    induction n with
    | zero => simp [hyperharmonic_succ]
    | succ n ihn =>
      have hrec : hyperharmonic (r + 1 + 1) (n + 1) =
          hyperharmonic (r + 1 + 1) n + hyperharmonic (r + 1) (n + 1) := by
        rw [hyperharmonic_succ (r + 1) (n + 1), hyperharmonic_succ (r + 1) n,
          Finset.sum_Icc_succ_top (Nat.succ_pos n)]
      rw [hrec, ihn, ihr (n + 1)]
      simpa only [Nat.succ_eq_add_one, Nat.add_right_comm n 1 r, ← Nat.add_assoc] using
        (choose_mul_harmonic_step (n + r + 1) r).symm

private theorem shifted_harmonic_sub_isEquivalent (r : ℕ) :
    (fun n : ℕ ↦ (harmonic (n + r) : ℝ) - harmonic r) ~[atTop] fun n : ℕ ↦ Real.log n := by
  have hshift : Tendsto (fun n : ℕ ↦ Real.log (↑(n + r)) - Real.log n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add] using
      (Real.tendsto_log_comp_add_sub_log (r : ℝ)).comp tendsto_natCast_atTop_atTop
  have hrem : Tendsto (fun n : ℕ ↦ ((harmonic (n + r) : ℝ) - harmonic r) - Real.log n)
      atTop (𝓝 (Real.eulerMascheroniConstant - (harmonic r : ℝ))) := by
    have h := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat r)
    simpa only [Function.comp_def, zero_add, sub_add_sub_cancel', sub_right_comm] using
      (hshift.add h).sub_const (harmonic r : ℝ)
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply IsLittleO.isEquivalent
  exact isLittleO_of_tendsto' ((hlog.eventually_gt_atTop 0).mono fun n hn hz ↦
    (hn.ne' hz).elim) (hrem.div_atTop hlog)

/-- **Asymptotic of the hyperharmonic numbers (Mező).** For every natural number $r \ge 1$, the
hyperharmonic numbers $h_n^{(r)}$ of order $r$ are asymptotically equivalent, as $n \to \infty$,
to $n^{r-1} \log n / (r-1)!$, where $\log$ is the natural logarithm:
$$h_n^{(r)} \sim \frac{n^{r-1} \log n}{(r-1)!} \qquad (n \to \infty).$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (`jis-2024-24.4.1-lem-1`). -/
public theorem hyperharmonic_isEquivalent (r : ℕ) (hr : 1 ≤ r) :
    (fun n : ℕ => (hyperharmonic r n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * Real.log n / (r - 1).factorial := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hyperharmonic_succ_eq_choose_mul,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub, Pi.mul_def, div_mul_eq_mul_div] using
    (isEquivalent_add_choose r).mul (shifted_harmonic_sub_isEquivalent r)

end MetaMathlibExt
