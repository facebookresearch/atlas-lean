/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ZeckendorfNewInformationZone
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Existence of the Zeckendorf digit-sum variation for shift one

For a Zeckendorf-adic integer $x$, the truncated variation for adding $1$ is eventually constant
exactly when the digits contain a pair of consecutive zeros at indices $j,j+1$ with $j\ge 2$.
Above the first such pair the odometer leaves all digits unchanged, so increasing the truncation
order does not change the variation. If there is no such pair, the digits alternate from index $2$
on, and adding $1$ gives the zero sequence. Then there are arbitrarily late truncations at which
including one more digit decreases the variation by $1$.

The alternating prefix before the first pair of zeros yields the two cylinders in
`zeckAdicVariation_one_exists_iff`: $C_{00(10)^d}$ for a first pair at $j=2d+2$, and
$C_{001(01)^d}$ for one at $j=2d+3$, with $d\ge 0$. Cylinder words are written from the
highest index to the lowest, with digit $x_2$ on the right.

## References

* Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
  An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
  (2024), Article 24.3.2, pp. 1–48, Section 2.2, Section 4, and Lemma 27 (first part, p. 27).
-/

namespace MetaMathlibExt

open Filter

private theorem eventually_const_iff_exists_zeroPair (x : ℕ → Bool) :
    (∃ d, ∀ᶠ k in atTop, zeckAdicTruncVariation 1 k x = d) ↔
      ∃ j, 2 ≤ j ∧ x j = false ∧ x (j + 1) = false := by
  constructor
  · rintro ⟨d, hd⟩
    by_contra h
    have hno (j : ℕ) : ¬(2 ≤ j ∧ x j = false ∧ x (j + 1) = false) := fun hj => h ⟨j, hj⟩
    obtain ⟨n, hn⟩ := eventually_atTop.mp hd
    let k := max n 1
    have hlate : ∃ j > k, x j = true := by
      have hk : 2 ≤ k + 1 := by dsimp [k]; omega
      cases h₁ : x (k + 1)
      · exact ⟨k + 2, by omega, Bool.eq_true_of_not_eq_false fun h₂ => hno _ ⟨hk, h₁, h₂⟩⟩
      · exact ⟨k + 1, by omega, h₁⟩
    obtain ⟨j, hj, hjx⟩ := hlate
    have hT : zeckOdometer x j = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      rcases zeckOdometer_apply_eq_true_iff.mp ht with ⟨hs, -⟩ | ⟨-, i, -, hs⟩
      · exact hno j hs
      · exact hno i hs
    have hn₁ : n ≤ j - 1 := le_trans (le_max_left n 1) (by omega)
    have hstep := zeckAdicTruncVariation_succ 1 x (k := j - 1)
      (le_trans (le_max_right n 1) (by omega))
    rw [show j - 1 + 1 = j by omega, Function.iterate_one, hT, hjx,
      hn _ (by omega), hn _ hn₁] at hstep
    simp at hstep
    omega
  · rintro ⟨j, hj⟩
    refine ⟨zeckAdicTruncVariation 1 j x, eventually_atTop.mpr ⟨j, fun k hk => ?_⟩⟩
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      have hT : zeckOdometer x (k + 1) = x (k + 1) := by
        apply Bool.eq_iff_iff.mpr
        rw [zeckOdometer_apply_eq_true_iff]
        constructor
        · rintro (⟨-, hmin⟩ | h)
          · exact (hmin j (by omega) hj).elim
          · exact h.1
        · exact fun h => Or.inr ⟨h, j, by omega, hj⟩
      simpa only [Function.iterate_one, hT, add_sub_cancel_right, ih] using
        zeckAdicTruncVariation_succ 1 x (k := k) (by have := hj.1; omega)

/-- **When the variation $\Delta^{(1)}$ exists.** Let $x$ be a Zeckendorf-adic integer with digits
$x_k$, and let $\Delta_k^{(1)}(x)$ be its truncated variation of order $k$ for $r = 1$. The
integer sequence $(\Delta_k^{(1)}(x))_k$ is eventually constant (equivalently, the variation
$\Delta^{(1)}(x) = \lim_{k \to \infty} \Delta_k^{(1)}(x)$ exists) if and only if there is
$d \ge 0$ such that either $x_{2d+3} = x_{2d+2} = 0$ and $x_{2i+1} = 1$, $x_{2i} = 0$ for
$1 \le i \le d$ (the cylinder $C_{00(10)^d}$), or $x_{2d+4} = x_{2d+3} = 0$, $x_{2d+2} = 1$ and
$x_{2i+1} = 0$, $x_{2i} = 1$ for $1 \le i \le d$ (the cylinder $C_{001(01)^d}$).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 27 (`jis-2024-24.3.2-lem-27`), first part. -/
public theorem zeckAdicVariation_one_exists_iff {x : ℕ → Bool} (hx : x ∈ zeckAdic) :
    (∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation 1 k x = d) ↔
      ∃ d : ℕ,
        (x (2 * d + 3) = false ∧ x (2 * d + 2) = false ∧
          ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = true ∧ x (2 * i) = false) ∨
        (x (2 * d + 4) = false ∧ x (2 * d + 3) = false ∧ x (2 * d + 2) = true ∧
          ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = false ∧ x (2 * i) = true) := by
  classical
  rw [eventually_const_iff_exists_zeroPair]
  constructor
  · intro h
    let j := Nat.find h
    obtain ⟨hj, hz, hz'⟩ := Nat.find_spec h
    have hnext (i : ℕ) (hi : 2 ≤ i) (hij : i < j) : x (i + 1) = !x i := by
      have hmin := Nat.find_min h hij
      cases hxi : x i
      · exact Bool.eq_true_of_not_eq_false fun hf => hmin ⟨hi, hxi, hf⟩
      · exact (mem_zeckAdic_iff.mp hx).2.2 i hi hxi
    have heven (m : ℕ) (hm : 2 * m + 2 ≤ j) : x (2 * m + 2) = x 2 := by
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [show 2 * (m + 1) + 2 = (2 * m + 2 + 1) + 1 by omega,
          hnext (2 * m + 2 + 1) (by omega) (by omega), hnext (2 * m + 2) (by omega) (by omega),
          Bool.not_not, ih (by omega)]
    have hpairs (d : ℕ) (hd : 2 * d + 2 ≤ j) (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
        x (2 * i + 1) = !x 2 ∧ x (2 * i) = x 2 := by
      have hi' : x (2 * i) = x 2 := by
        rw [show 2 * i = 2 * (i - 1) + 2 by omega, heven _ (by omega)]
      exact ⟨(hnext (2 * i) (by omega) (by omega)).trans (congrArg Bool.not hi'), hi'⟩
    let d := (j - 2) / 2
    have hj' : j = 2 * d + 2 ∨ j = 2 * d + 3 := by dsimp only [d]; omega
    refine ⟨d, ?_⟩
    rcases hj' with hj' | hj'
    · rw [show Nat.find h = j from rfl, hj'] at hz hz'
      have h₂ : x 2 = false := (heven d (by omega)).symm.trans hz
      exact Or.inl ⟨hz', hz, fun i hi hid => by simpa [h₂] using hpairs d (by omega) i hi hid⟩
    · rw [show Nat.find h = j from rfl, hj'] at hz hz'
      have he := heven d (by omega)
      have ho := hnext (2 * d + 2) (by omega) (by omega)
      rw [he, show 2 * d + 2 + 1 = 2 * d + 3 by omega, hz] at ho
      have h₂ : x 2 = true := Bool.eq_true_of_not_eq_false' ho.symm
      exact Or.inr ⟨hz', hz, he.trans h₂, fun i hi hid => by
        simpa [h₂] using hpairs d (by omega) i hi hid⟩
  · rintro ⟨d, ⟨h₃, h₂, -⟩ | ⟨h₄, h₃, -, -⟩⟩
    · exact ⟨2 * d + 2, by omega, h₂, h₃⟩
    · exact ⟨2 * d + 3, by omega, h₃, h₄⟩

end MetaMathlibExt
