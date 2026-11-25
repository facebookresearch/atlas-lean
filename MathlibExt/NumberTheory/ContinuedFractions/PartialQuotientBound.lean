/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic.LinearCombination

/-!
# Lower bounds for continued-fraction approximation

A bound on the partial quotients up to the relevant index gives a strict lower bound on the
error of any rational approximation with denominator below the cutoff.
-/

namespace MetaMathlibExt

open GenContFract

namespace one_div_partialQuotient_bound_mul_lt_abs_mul_sub

/-- Express an integer pair in the basis of the current and preceding continuants. -/
private theorem exists_continuant_coefficients {γ : ℝ}
    (hinf : ∀ k, ¬(GenContFract.of γ).TerminatedAt k) (x y : ℤ) (n : ℕ) :
    ∃ u v : ℤ,
      (x : ℝ) = u * ((GenContFract.of γ).contsAux (n + 1)).b +
        v * ((GenContFract.of γ).contsAux n).b ∧
      (y : ℝ) = u * ((GenContFract.of γ).contsAux (n + 1)).a +
        v * ((GenContFract.of γ).contsAux n).a := by
  induction n with
  | zero =>
    refine ⟨x, y - x * ⌊γ⌋, ?_⟩
    simp [of_h_eq_floor]
  | succ n ih =>
    obtain ⟨u, v, hx, hy⟩ := ih
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp (hinf n)
    obtain ⟨h₁, d, hd⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
    refine ⟨v, u - v * d, ?_⟩
    rw [contsAux_recurrence hgp rfl rfl, h₁, hd, Int.cast_sub, Int.cast_mul]
    constructor
    · rw [hx]
      ring
    · rw [hy]
      ring

/-- Below the next denominator, the error multiplier has absolute value at least one. -/
private theorem one_le_abs_of_den_lt_next {u v d : ℤ} {Q R t : ℝ}
    (hQ : 0 < Q) (hR : 0 ≤ R) (ht : 0 ≤ t) (hdt : (d : ℝ) ≤ t)
    (hpos : 0 < u * Q + v * R) (hnext : u * Q + v * R < d * Q + R) :
    1 ≤ |(u : ℝ) - v * t| := by
  by_cases hv : v ≤ 0
  · have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast hv
    have hu : 0 < u := by
      by_contra! h
      have hu' : (u : ℝ) ≤ 0 := by exact_mod_cast h
      linarith [mul_nonpos_of_nonpos_of_nonneg hu' hQ.le,
        mul_nonpos_of_nonpos_of_nonneg hv' hR]
    have hu' : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
    calc
      1 ≤ (u : ℝ) - v * t := by linarith [mul_nonpos_of_nonpos_of_nonneg hv' ht]
      _ ≤ _ := le_abs_self _
  · have hv' : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    have hu : u < d := by
      by_contra! h
      have hu' : (d : ℝ) ≤ u := by exact_mod_cast h
      linarith [mul_le_mul_of_nonneg_right hu' hQ.le, mul_le_mul_of_nonneg_right hv' hR]
    have hu' : (u : ℝ) + 1 ≤ d := by exact_mod_cast (show u + 1 ≤ d by omega)
    calc
      1 ≤ -((u : ℝ) - v * t) := by linarith [mul_le_mul_of_nonneg_right hv' ht]
      _ ≤ _ := neg_le_abs _

end one_div_partialQuotient_bound_mul_lt_abs_mul_sub

open one_div_partialQuotient_bound_mul_lt_abs_mul_sub in
-- Keep the original named hypotheses hM, hNM and ha0.
set_option linter.unusedVariables false in
/-- **Partial-quotient lower bound for rational approximation.** Let $\gamma$ be an irrational real
number with continued fraction $[a_0; a_1, a_2, \dots]$, so that $a_0 = \lfloor \gamma \rfloor$,
and let $q_0 = 1, q_1, q_2, \dots$ be the denominators of its convergents. Let $M \ge 1$ and
$N \ge 0$ be integers with $q_N \le M < q_{N+1}$, and let $A$ be a real number with $a_i \le A$
for $0 \le i \le N + 1$. Then $|x \gamma - y| > 1/((A + 2) x)$ for all integers $x, y$ with
$0 < x < M$.

Taking $A = \max(a_0, \dots, a_{N+1})$ gives the strongest bound.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Lemma 2 (`integers-2025-A55-lem-2`). -/
public theorem one_div_partialQuotient_bound_mul_lt_abs_mul_sub {γ : ℝ}
    (hγ : Irrational γ) {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of γ).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of γ).dens (N + 1)) {aL : ℝ} (ha0 : (⌊γ⌋ : ℝ) ≤ aL)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of γ).partDens.get? j = some b → b ≤ aL)
    {x y : ℤ} (hx : 0 < x) (hxM : x < M) :
    1 / ((aL + 2) * x) < |x * γ - y| := by
  let g := GenContFract.of γ
  have hinf (k : ℕ) : ¬g.TerminatedAt k := by
    intro hk
    obtain ⟨r, hr⟩ := exists_rat_eq_of_terminates ⟨k, hk⟩
    exact hγ ⟨r, hr.symm⟩
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hxM' : (x : ℝ) < M := by exact_mod_cast hxM
  -- Choose the first convergent whose successor has denominator greater than x.
  have hex : ∃ n, (x : ℝ) < g.dens (n + 1) := ⟨N, hxM'.trans hMN⟩
  let n := Nat.find hex
  have hnN : n ≤ N := Nat.find_min' hex (hxM'.trans hMN)
  have hxnext : (x : ℝ) < g.dens (n + 1) := Nat.find_spec hex
  have hden_le : g.dens n ≤ (x : ℝ) := by
    cases hn : n with
    | zero =>
      rw [zeroth_den_eq_one]
      exact_mod_cast (show 1 ≤ x by omega)
    | succ k =>
      exact le_of_not_gt (Nat.find_min hex (show k < n by omega))
  let C := g.contsAux (n + 1)
  let P := g.contsAux n
  have hC : 0 < C.b := (Nat.cast_pos.mpr (Nat.fib_pos.mpr n.succ_pos)).trans_le
    (succ_nth_fib_le_of_nth_den (Or.inr (hinf (n - 1))))
  have hP : 0 ≤ P.b := zero_le_of_contsAux_b
  have hPC : P.b ≤ C.b := by
    cases hn : n with
    | zero => simp [P, C, hn]
    | succ k =>
      simp only [P, C, hn]
      exact of_den_mono (v := γ) (n := k)
  obtain ⟨next, hnext⟩ := Option.ne_none_iff_exists'.mp
    (mt of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr (hinf n))
  obtain ⟨s, hs, hs₀, htail⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hnext
  let t := s.fr⁻¹
  have hpart := partDen_eq_s_b (get?_of_eq_some_of_succ_get?_intFractPair_stream hnext)
  have hd : (1 : ℝ) ≤ next.b := of_one_le_get?_partDen hpart
  have hda : (next.b : ℝ) ≤ aL := ha n hnN _ hpart
  have hdt : (next.b : ℝ) ≤ t := IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv hs hnext
  have ht : 0 < t := zero_lt_one.trans_le (hd.trans hdt)
  have hta : t < aL + 1 := by
    have hfloor : ⌊t⌋ = next.b := congrArg IntFractPair.b htail
    exact (Int.lt_floor_add_one t).trans_le (by rw [hfloor]; linarith)
  have hA : 0 < aL + 2 := by linarith
  have hsum : 0 < t * C.b + P.b := by positivity
  have hbound : t * C.b + P.b < (aL + 2) * x := calc
    _ < (aL + 1) * C.b + C.b := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right hta hC) hPC
    _ = (aL + 2) * C.b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden_le hA.le
  -- Convert the exact convergent error formula to the error before division by the denominator.
  have hconv : |C.b * γ - C.a| = 1 / (t * C.b + P.b) := by
    have he : C.b * γ - C.a = C.b * (γ - g.convs n) := by
      rw [conv_eq_num_div_den]
      change _ = C.b * (γ - C.a / C.b)
      field_simp
    have hformula : γ - g.convs n = (-1) ^ n / (C.b * (t * C.b + P.b)) := by
      simpa only [hs₀, ite_false] using sub_convs_eq hs
    rw [he, abs_mul, abs_of_pos hC, hformula, abs_div, abs_neg_one_pow,
      abs_of_pos (mul_pos hC hsum)]
    field_simp
  have hexact : γ = (t * C.a + P.a) / (t * C.b + P.b) := by
    simpa [GenContFract.compExactValue, hs₀, nextConts, nextNum, nextDen, C, P, g, t]
      using compExactValue_correctness_of_stream_eq_some hs
  have hrel : P.b * γ - P.a = -t * (C.b * γ - C.a) := by
    linear_combination (eq_div_iff hsum.ne').mp hexact
  obtain ⟨u, v, hxuv, hyuv⟩ := exists_continuant_coefficients hinf x y n
  change (x : ℝ) = u * C.b + v * P.b at hxuv
  change (y : ℝ) = u * C.a + v * P.a at hyuv
  have hnextden : g.dens (n + 1) = (next.b : ℝ) * C.b + P.b := by
    change (g.contsAux (n + 2)).b = _
    rw [contsAux_recurrence (get?_of_eq_some_of_succ_get?_intFractPair_stream hnext) rfl rfl]
    simp [C, P, g]
  have hcoeff := one_le_abs_of_den_lt_next hC hP ht.le hdt
    (hxuv ▸ hx') (by rwa [← hxuv, ← hnextden])
  have herr : (x : ℝ) * γ - y = (u - v * t) * (C.b * γ - C.a) := by
    linear_combination γ * hxuv - hyuv + v * hrel
  calc
    _ < |C.b * γ - C.a| := hconv ▸ one_div_lt_one_div_of_lt hsum hbound
    _ ≤ |(x : ℝ) * γ - y| := by
      rw [herr, abs_mul]
      simpa using mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (C.b * γ - C.a))

end MetaMathlibExt
