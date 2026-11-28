/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FibonacciGeneratingFunctionsKnappMRelations
import all MathlibExt.NumberTheory.FibonacciGeneratingFunctions
import all MathlibExt.NumberTheory.SecondOrderMValueSmallNonneg
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Set.Function
import Mathlib.Order.WellFounded
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Classification of good families for Gibonacci generating functions

Let `a, b` be integers not both zero and let `D = a² + ab - b²`. Every pair of integers `M, k`
with `k ≠ 0` and `M² = 5k² + (2b - 6a)k + (a - b)²` gives a good rational value
`x = (a - b - k + M) / (2k)`, where the generating function equals `k`. The printed Theorem 4
restricts its candidates to `M` within the search bound for which the auxiliary quadratic
has an integer solution `N`. The root formula in Section 3, equations (5)–(6), gives goodness
without either restriction. For completeness, start with a good fraction `p / q` with
`gcd(p, q) = 1` and `q ≠ 0`. If its two-sided family contains neither the rational number `0`
nor a zero of the generating function, it has a representative of the displayed form with
`M² + 3MN + N² = D` for an integer `N`, and with `M² ≤ -D` when `D < 0` or `5M² ≤ D` when `D > 0`.

## References

* Michael P. Knapp, [*Fibonacci Generating Functions*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Knapp/knapp5.pdf),
  Journal of Integer Sequences 27 (2024), Article 24.3.1, pp. 1–12, Theorem 4 for the completeness
  of the bounded search and Section 3, equations (5)–(6), for goodness without the candidate
  restrictions. The proof also uses Theorem 1, the identities of Lemma 11, and the minimum argument
  of Lemmas 12 and 13.
* Prapanpong Pongsriiam, *Integral Values of the Generating Functions of Fibonacci and Lucas
  Numbers*, The College Mathematics Journal 48(2) (2017), pp. 97–101, for the discriminant method
  credited by Knapp in Section 3.
* The Lean proof uses `gibonacci_denom_ne_zero` and `isGibonacciGood_transform` from
  `MathlibExt.NumberTheory.FibonacciGeneratingFunctions`, `knappM_recurrence_and_quadratic`
  from `MathlibExt.NumberTheory.FibonacciGeneratingFunctionsKnappMRelations`, and
  `exists_small_secondOrderMValue_of_nonneg.exists_intCast_eq_of_sq_eq` from
  `MathlibExt.NumberTheory.SecondOrderMValueSmallNonneg` to deduce integrality from the square.
-/

namespace MetaMathlibExt

open Function Set

private theorem fibonacciPairOrbit_mapsTo (v : ℤ × ℤ) :
    MapsTo fibonacciPairStep (fibonacciPairOrbit v) (fibonacciPairOrbit v) ∧
      MapsTo fibonacciPairStepBack (fibonacciPairOrbit v) (fibonacciPairOrbit v) := by
  constructor
  · intro w hw
    rcases hw with ⟨n, rfl | rfl⟩
    · exact ⟨n + 1, Or.inl (iterate_succ_apply' _ n v).symm⟩
    · cases n with
      | zero => exact ⟨1, Or.inl rfl⟩
      | succ n => exact ⟨n, Or.inr (by rw [iterate_succ_apply', fibonacciPairStep_stepBack])⟩
  · intro w hw
    rcases hw with ⟨n, rfl | rfl⟩
    · cases n with
      | zero => exact ⟨1, Or.inr rfl⟩
      | succ n => exact ⟨n, Or.inl (by rw [iterate_succ_apply', fibonacciPairStepBack_step])⟩
    · exact ⟨n + 1, Or.inr (iterate_succ_apply' _ n v).symm⟩

private theorem fibonacciPairOrbit_subset {v : ℤ × ℤ} {s : Set (ℤ × ℤ)}
    (hf : MapsTo fibonacciPairStep s s) (hb : MapsTo fibonacciPairStepBack s s) (hv : v ∈ s) :
    fibonacciPairOrbit v ⊆ s := by
  rintro _ ⟨n, rfl | rfl⟩
  · exact hf.iterate n hv
  · exact hb.iterate n hv

-- Complete the square after clearing the (nonzero) generating-function denominator.
private theorem knapp_discriminant_iff (a b : ℤ) (x k : ℚ) (hk : k ≠ 0) :
    (k * (2 * x + 1) - a + b) ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 ↔
      gibonacciGeneratingValue a b x = k := by
  rw [gibonacciGeneratingValue, div_eq_iff (gibonacci_denom_ne_zero x)]
  constructor
  · intro h
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hk)
    linear_combination h
  · intro h
    linear_combination (4 * k) * h

private theorem knappM_eq_signed_root (a b p q : ℤ) (hq : q ≠ 0) :
    knappM a b p q =
      gibonacciGeneratingValue a b ((p : ℚ) / q) * (2 * ((p : ℚ) / q) + 1) - a + b := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  let d : ℚ := (q : ℚ) ^ 2 - p * q - (p : ℚ) ^ 2
  have hden : 1 - (p : ℚ) / q - ((p : ℚ) / q) ^ 2 = d / (q : ℚ) ^ 2 := by
    dsimp [d]
    field_simp
  have hd : d ≠ 0 := (div_ne_zero_iff.mp (hden ▸ gibonacci_denom_ne_zero ((p : ℚ) / q))).1
  unfold knappM gibonacciGeneratingValue
  rw [hden]
  change (2 * (p : ℚ) + q) * (((b : ℚ) - a) * p + (a : ℚ) * q) / d - a + b = _
  field_simp

-- If the center has least absolute value, the invariant lies outside the gap
-- between `-M²` and `5M²`.
private theorem knapp_bounds_of_minimum (M N : ℤ) (hN : M ^ 2 ≤ N ^ 2)
    (hprev : M ^ 2 ≤ (3 * M + N) ^ 2) :
    5 * M ^ 2 ≤ M ^ 2 + 3 * M * N + N ^ 2 ∨ M ^ 2 + 3 * M * N + N ^ 2 ≤ -M ^ 2 := by
  wlog hM : 0 ≤ M generalizing M N
  · have hprev' : (-M) ^ 2 ≤ (3 * (-M) + (-N)) ^ 2 := by
      rwa [show 3 * (-M) + (-N) = -(3 * M + N) by ring, neg_sq, neg_sq]
    simpa only [neg_sq, mul_neg, neg_mul, neg_neg] using
      this (-M) (-N) (by simpa only [neg_sq] using hN) hprev' (by omega)
  have hsign (z : ℤ) (h : M ^ 2 ≤ z ^ 2) : M ≤ z ∨ z ≤ -M := by
    have ha := sq_le_sq.mp h
    rw [abs_of_nonneg hM] at ha
    rcases le_or_gt 0 z with hz | hz
    · exact Or.inl (by rwa [abs_of_nonneg hz] at ha)
    · rw [abs_of_neg hz] at ha
      exact Or.inr (by omega)
  rcases hsign N hN with h | h
  · exact Or.inl (by nlinarith only [mul_nonneg (show 0 ≤ N - M by omega)
                      (show 0 ≤ N + 4 * M by omega)])
  rcases hsign (3 * M + N) hprev with h' | h'
  · exact Or.inr (by nlinarith only [mul_nonpos_of_nonpos_of_nonneg
                      (show N + M ≤ 0 by omega) (show 0 ≤ N + 2 * M by omega)])
  · exact Or.inl (by nlinarith only [mul_nonneg_of_nonpos_of_nonpos
                      (show N - M ≤ 0 by omega) (show N + 4 * M ≤ 0 by omega)])

-- Keep the nonzero seed assumption of Theorem 4; the implications in the bound need no case D = 0.
set_option linter.unusedVariables false in
/-- For `(a, b) ≠ (0, 0)`, (i) every integer solution `(M, k)`,
`k ≠ 0`, of `M² = 5k² + (2b - 6a)k + (a - b)²` gives a good value
`x = (a - b - k + M) / 2k` (whose family is good by Theorem 1); (ii) every
family of good values other than the Fibonacci family (the one containing
`0`) and the family containing a zero of `G^{(a,b)}` has a member
`x = (a - b - k + M) / 2k` with `k ≠ 0`, `M² = 5k² + (2b - 6a)k + (a - b)²`,
`|M| ≤ C` (written `M² ≤ |a² + ab - b²|` if `a² + ab - b² < 0` and
`5M² ≤ a² + ab - b²` if it is positive) and an integer `N` with
`M² + 3MN + N² = a² + ab - b²`.

The printed Theorem 4 asserts goodness only for candidates whose `M` satisfies
both the search bound and the auxiliary quadratic equation for some integer `N`.
Part (i) drops those two restrictions by the root formula in Section 3,
equations (5)–(6). Part (ii) is the completeness claim of Theorem 4.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 4 (`jis-2024-24.3.1-thm-4`). -/
public theorem gibonacci_good_families_classification (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    (∀ M k : ℤ, k ≠ 0 → M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 →
        IsGibonacciGood a b (((a - b - k + M : ℤ) : ℚ) / (2 * k))) ∧
      ∀ p q : ℤ, Int.gcd p q = 1 → q ≠ 0 → IsGibonacciGood a b ((p : ℚ) / q) →
        (∀ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 →
          (v.1 : ℚ) / v.2 ≠ 0 ∧ gibonacciGeneratingValue a b ((v.1 : ℚ) / v.2) ≠ 0) →
        ∃ v ∈ fibonacciPairOrbit (p, q), v.2 ≠ 0 ∧ ∃ M k N : ℤ, k ≠ 0 ∧
          (a ^ 2 + a * b - b ^ 2 < 0 → M ^ 2 ≤ -(a ^ 2 + a * b - b ^ 2)) ∧
          (0 < a ^ 2 + a * b - b ^ 2 → 5 * M ^ 2 ≤ a ^ 2 + a * b - b ^ 2) ∧
          M ^ 2 + 3 * M * N + N ^ 2 = a ^ 2 + a * b - b ^ 2 ∧
          M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 ∧
          (v.1 : ℚ) / v.2 = ((a - b - k + M : ℤ) : ℚ) / (2 * k) := by
  constructor
  · intro M k hk hdisc
    let x : ℚ := ((a - b - k + M : ℤ) : ℚ) / (2 * k)
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    have hM : (M : ℚ) = (k : ℚ) * (2 * x + 1) - a + b := by
      dsimp [x]
      push_cast
      field_simp
      ring
    refine ⟨gibonacci_denom_ne_zero x, k, (knapp_discriminant_iff a b x k hk').mp ?_⟩
    rw [← hM]
    exact_mod_cast hdisc
  intro p q hcop hq hgood hexcept
  classical
  let orbit := fibonacciPairOrbit (p, q)
  have hseed : (p, q) ∈ orbit := ⟨0, Or.inl rfl⟩
  let next (v : orbit) : orbit := ⟨fibonacciPairStep v, (fibonacciPairOrbit_mapsTo _).1 v.2⟩
  let prev (v : orbit) : orbit := ⟨fibonacciPairStepBack v, (fibonacciPairOrbit_mapsTo _).2 v.2⟩
  have hcopOrbit (v : orbit) : IsCoprime v.1.1 v.1.2 := by
    apply fibonacciPairOrbit_subset (s := {w | IsCoprime w.1 w.2}) ?_ ?_
      (Int.isCoprime_iff_gcd_eq_one.mpr hcop) v.2
    · intro w (hw : IsCoprime w.1 w.2)
      simpa only [Set.mem_ofPred_eq, fibonacciPairStep, Prod.fst, Prod.snd, one_mul] using
        hw.symm.add_mul_right_right (1 : ℤ)
    · intro w (hw : IsCoprime w.1 w.2)
      simpa only [Set.mem_ofPred_eq, fibonacciPairStepBack, Prod.fst, Prod.snd, one_mul] using
        (IsCoprime.sub_mul_right_left_iff (z := (1 : ℤ))).mpr hw.symm
  -- A pair with second coordinate zero would give the forbidden fraction zero at the next step.
  have hnonzero (v : orbit) : v.1.2 ≠ 0 := by
    intro hv
    have hc := hcopOrbit v
    rw [hv] at hc
    have hp := (isCoprime_zero_right.mp hc).ne_zero
    have hnext : (next v).1.2 ≠ 0 := by simpa [next, fibonacciPairStep, hv] using hp
    exact (hexcept (next v) (next v).2 hnext).1 (by simp [next, fibonacciPairStep, hv])
  have hgoodOrbit (v : orbit) : IsGibonacciGood a b ((v.1.1 : ℚ) / v.1.2) := by
    let s : Set (ℤ × ℤ) := {w | w ∈ orbit ∧ IsGibonacciGood a b ((w.1 : ℚ) / w.2)}
    have hstep {w : ℤ × ℤ} (hw : w ∈ s) :=
      isGibonacciGood_transform a b w.1 w.2
        (Int.isCoprime_iff_gcd_eq_one.mp (hcopOrbit ⟨w, hw.1⟩)) (hnonzero ⟨w, hw.1⟩) hw.2
    apply (fibonacciPairOrbit_subset (s := s) ?_ ?_ ⟨hseed, hgood⟩ v.2).2
    · intro w hw
      let w' := next ⟨w, hw.1⟩
      exact ⟨w'.2, by
        simpa only [fibonacciPairStep, Int.cast_add] using (hstep hw).1 (hnonzero w')⟩
    · intro w hw
      let w' := prev ⟨w, hw.1⟩
      exact ⟨w'.2, by
        simpa only [fibonacciPairStepBack, Int.cast_sub] using (hstep hw).2 (hnonzero w')⟩
  have hdata (v : orbit) : ∃ k M : ℤ, k ≠ 0 ∧ knappM a b v.1.1 v.1.2 = M ∧
      M ^ 2 = 5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 ∧
      (v.1.1 : ℚ) / v.1.2 = ((a - b - k + M : ℤ) : ℚ) / (2 * k) := by
    obtain ⟨_, k, hk⟩ := hgoodOrbit v
    have hk' : (k : ℚ) ≠ 0 := hk ▸ (hexcept v v.2 (hnonzero v)).2
    have hM := knappM_eq_signed_root a b v.1.1 v.1.2 (hnonzero v)
    rw [hk] at hM
    have hdisc := (knapp_discriminant_iff a b _ k hk').mpr hk
    rw [← hM] at hdisc
    have hdisc' : knappM a b v.1.1 v.1.2 ^ 2 =
        ((5 * k ^ 2 + (2 * b - 6 * a) * k + (a - b) ^ 2 : ℤ) : ℚ) := by
      push_cast
      exact hdisc
    obtain ⟨M, hcast⟩ := exists_small_secondOrderMValue_of_nonneg.exists_intCast_eq_of_sq_eq hdisc'
    rw [hcast] at hM hdisc'
    refine ⟨k, M, by exact_mod_cast hk', hcast, by exact_mod_cast hdisc', ?_⟩
    have h2k : 2 * (k : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hk'
    rw [eq_div_iff h2k]
    push_cast
    linear_combination -hM
  choose k μ hk hμ hdisc hfrac using hdata
  have : Nonempty orbit := ⟨⟨(p, q), hseed⟩⟩
  let size (w : orbit) : ℕ := (μ w).natAbs
  let v := Function.argmin size
  have hmin (w : orbit) : μ v ^ 2 ≤ μ w ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (le_of_not_gt (Function.not_lt_argmin size w))
  let m (w : orbit) : ℚ := knappM a b w.1.1 w.1.2
  have hrel (w : orbit) : m (next (next w)) = -3 * m (next w) - m w ∧
      m w ^ 2 + 3 * m w * m (next w) + m (next w) ^ 2 =
        ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ) := by
    have h := knappM_recurrence_and_quadratic a b w.1.1 w.1.2
      (fun e => hnonzero w (congrArg Prod.snd e))
    simpa only [m, next, fibonacciPairStep, show w.1.2 + (w.1.1 + w.1.2) =
      w.1.1 + 2 * w.1.2 by ring] using h
  have hcast (w : orbit) : m w = (μ w : ℚ) := hμ w
  have hquad := (hrel v).2
  rw [hcast v, hcast (next v)] at hquad
  have hquad' : μ v ^ 2 + 3 * μ v * μ (next v) + μ (next v) ^ 2 = a ^ 2 + a * b - b ^ 2 := by
    exact_mod_cast hquad
  have hprev : μ (prev v) = -(3 * μ v + μ (next v)) := by
    have hundo : next (prev v) = v := Subtype.ext (fibonacciPairStep_stepBack v)
    have h := (hrel (prev v)).1
    rw [hundo, hcast (next v), hcast v, hcast (prev v)] at h
    have h' : μ (next v) = -3 * μ v - μ (prev v) := by exact_mod_cast h
    omega
  have hprevMin := hmin (prev v)
  rw [hprev, neg_sq] at hprevMin
  have hbound := knapp_bounds_of_minimum (μ v) (μ (next v)) (hmin (next v)) hprevMin
  rw [hquad'] at hbound
  refine ⟨v, v.2, hnonzero v, μ v, k v, μ (next v), hk v, ?_, ?_, hquad', hdisc v, hfrac v⟩
  · intro hD
    rcases hbound with h | h <;> nlinarith only [hD, h, sq_nonneg (μ v)]
  · intro hD
    rcases hbound with h | h
    · exact h
    · nlinarith only [hD, h, sq_nonneg (μ v)]

end MetaMathlibExt
