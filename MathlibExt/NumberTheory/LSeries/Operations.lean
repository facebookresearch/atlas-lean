/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# L-series of power twists and of square-supported lifts

Two operations on coefficient sequences act on Dirichlet series by a change of variable.

* Weighting the coefficients by `n ^ a` shifts the argument by `a`:
  `L (fun n ↦ f n * n ^ a) s = L f (s - a)`, with no hypotheses at all, and the same holds for
  absolute convergence.
* Moving the coefficients onto the squares, `n ↦ f (√n)` if `n` is a square and `0` otherwise,
  doubles the argument: `L (squareLift f) s = L f (2 * s)`, and again the same holds for
  absolute convergence.

## Main definitions

* `ArithmeticFunction.squareLift`: the arithmetic function `m ^ 2 ↦ f m`, vanishing off the
  squares.

## Main statements

* `LSeries.term_mul_cpow`, `LSeries_mul_cpow`, `LSeriesSummable_mul_cpow_iff`: the exponent shift.
* `LSeries_cpow_eq_riemannZeta`, `LSeriesSummable_cpow_iff`: the Dirichlet series of `n ^ a` is
  `ζ (s - a)`.
* `ArithmeticFunction.IsMultiplicative.squareLift`: square-supported lifts of multiplicative
  functions are multiplicative.
* `ArithmeticFunction.LSeries_squareLift`, `ArithmeticFunction.LSeriesSummable_squareLift_iff`:
  the argument doubling.
-/

@[expose] public section

open scoped LSeries.notation

/-! ### The exponent shift -/

/-- Weighting the coefficients by `n ^ a` shifts the argument of every term of a Dirichlet series
by `a`. -/
theorem LSeries.term_mul_cpow (f : ℕ → ℂ) (a s : ℂ) (n : ℕ) :
    LSeries.term (fun m ↦ f m * (m : ℂ) ^ a) s n = LSeries.term f (s - a) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn), div_div_eq_mul_div]

/-- Weighting the coefficients by `n ^ a` shifts the argument of a Dirichlet series by `a`. No
convergence hypothesis is needed: the two series have the same terms. -/
theorem LSeries_mul_cpow (f : ℕ → ℂ) (a s : ℂ) :
    LSeries (fun n ↦ f n * (n : ℂ) ^ a) s = LSeries f (s - a) :=
  tsum_congr (LSeries.term_mul_cpow f a s)

/-- Weighting the coefficients by `n ^ a` shifts the region of absolute convergence of a
Dirichlet series by `a`. -/
theorem LSeriesSummable_mul_cpow_iff (f : ℕ → ℂ) (a s : ℂ) :
    LSeriesSummable (fun n ↦ f n * (n : ℂ) ^ a) s ↔ LSeriesSummable f (s - a) :=
  summable_congr (LSeries.term_mul_cpow f a s)

/-- The Dirichlet series `∑ n ^ a / n ^ s` converges absolutely exactly when
`1 < re (s - a)`. -/
theorem LSeriesSummable_cpow_iff {a s : ℂ} :
    LSeriesSummable (fun n : ℕ ↦ (n : ℂ) ^ a) s ↔ 1 < (s - a).re := by
  have h := LSeriesSummable_mul_cpow_iff 1 a s
  simp only [Pi.one_apply, one_mul] at h
  rw [h, LSeriesSummable_one_iff]

/-- For `1 < re (s - a)`, the Dirichlet series `∑ n ^ a / n ^ s` is `ζ (s - a)`. -/
theorem LSeries_cpow_eq_riemannZeta {a s : ℂ} (h : 1 < (s - a).re) :
    LSeries (fun n : ℕ ↦ (n : ℂ) ^ a) s = riemannZeta (s - a) := by
  have e := LSeries_mul_cpow 1 a s
  simp only [Pi.one_apply, one_mul] at e
  rw [e, LSeries_one_eq_riemannZeta h]

/-! ### Square-supported lifts -/

namespace ArithmeticFunction

variable {R : Type*}

/-- The square-supported lift of an arithmetic function: `squareLift f (m ^ 2) = f m`, and
`squareLift f n = 0` when `n` is not a square. -/
def squareLift [Zero R] (f : ArithmeticFunction R) : ArithmeticFunction R where
  toFun n := if IsSquare n then f n.sqrt else 0
  map_zero' := by simp

/-- The defining formula for `ArithmeticFunction.squareLift`. -/
theorem squareLift_apply [Zero R] (f : ArithmeticFunction R) (n : ℕ) :
    f.squareLift n = if IsSquare n then f n.sqrt else 0 :=
  rfl

/-- The square-supported lift takes the value `f m` at `m ^ 2`. -/
@[simp]
theorem squareLift_apply_sq [Zero R] (f : ArithmeticFunction R) (m : ℕ) :
    f.squareLift (m ^ 2) = f m := by
  rw [squareLift_apply, ite_eq_left ⟨m, sq m⟩, Nat.sqrt_eq']

/-- The square-supported lift vanishes off the squares. -/
theorem squareLift_apply_of_not_isSquare [Zero R] (f : ArithmeticFunction R) {n : ℕ}
    (hn : ¬ IsSquare n) : f.squareLift n = 0 := by
  rw [squareLift_apply, ite_eq_right hn]

/-- A product of coprime natural numbers is a square exactly when both factors are. -/
theorem _root_.Nat.Coprime.isSquare_mul_iff {m n : ℕ} (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  refine ⟨fun hmn ↦ ?_, fun ⟨hm, hn⟩ ↦ hm.mul hn⟩
  rw [isSquare_iff_exists_sq] at hmn
  obtain ⟨c, hc⟩ := hmn
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) hc
  obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h.symm)
    (by rw [mul_comm]; exact hc)
  exact ⟨isSquare_iff_exists_sq _ |>.mpr ⟨d, hd⟩, isSquare_iff_exists_sq _ |>.mpr ⟨e, he⟩⟩

/-- The square-supported lift of a multiplicative function is multiplicative. -/
theorem IsMultiplicative.squareLift [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) : f.squareLift.IsMultiplicative := by
  refine ⟨by simpa using f.squareLift_apply_sq 1 ▸ hf.map_one, fun {m n} hmn ↦ ?_⟩
  by_cases hm : IsSquare m
  · by_cases hn : IsSquare n
    · obtain ⟨u, rfl⟩ := hm
      obtain ⟨v, rfl⟩ := hn
      have huv : u.Coprime v :=
        Nat.Coprime.coprime_mul_left (Nat.Coprime.coprime_mul_left_right hmn)
      rw [show u * u * (v * v) = (u * v) ^ 2 by ring, ← sq, ← sq, squareLift_apply_sq,
        squareLift_apply_sq, squareLift_apply_sq, hf.map_mul_of_coprime huv]
    · rw [squareLift_apply_of_not_isSquare _ hn, mul_zero,
        squareLift_apply_of_not_isSquare _ (by rw [hmn.isSquare_mul_iff]; tauto)]
  · rw [squareLift_apply_of_not_isSquare _ hm, zero_mul,
      squareLift_apply_of_not_isSquare _ (by rw [hmn.isSquare_mul_iff]; tauto)]

private theorem term_squareLift_comp_sq (f : ArithmeticFunction ℂ) (s : ℂ) (m : ℕ) :
    LSeries.term (↗f.squareLift) s (m ^ 2) = LSeries.term (↗f) (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hm), LSeries.term_of_ne_zero hm,
      squareLift_apply_sq, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num,
      Complex.natCast_cpow_natCast_mul, Nat.cast_pow]

private theorem term_squareLift_eq_zero (f : ArithmeticFunction ℂ) (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ ↦ m ^ 2)) : LSeries.term (↗f.squareLift) s n = 0 := by
  have hsq : ¬ IsSquare n := by
    rintro ⟨r, rfl⟩
    exact hn ⟨r, sq r⟩
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · rw [LSeries.term_of_ne_zero h0, squareLift_apply_of_not_isSquare _ hsq, zero_div]

private theorem sq_injective : Function.Injective (fun m : ℕ ↦ m ^ 2) :=
  fun _ _ h ↦ Nat.pow_left_injective two_ne_zero h

/-- Moving the coefficients onto the squares doubles the argument of a Dirichlet series:
`L (squareLift f) s = L f (2 * s)`. -/
theorem LSeries_squareLift (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (↗f.squareLift) s = LSeries (↗f) (2 * s) := by
  rw [LSeries, ← sq_injective.tsum_eq fun n hn ↦ by_contra fun h ↦
    hn (term_squareLift_eq_zero f s h)]
  exact tsum_congr (term_squareLift_comp_sq f s)

/-- The square-supported lift of `f` has an absolutely convergent Dirichlet series at `s`
exactly when `f` has one at `2 * s`. -/
theorem LSeriesSummable_squareLift_iff (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (↗f.squareLift) s ↔ LSeriesSummable (↗f) (2 * s) := by
  rw [LSeriesSummable, ← sq_injective.summable_iff fun n hn ↦ term_squareLift_eq_zero f s hn]
  exact summable_congr (term_squareLift_comp_sq f s)

end ArithmeticFunction
