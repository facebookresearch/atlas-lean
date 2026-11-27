/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.QuadraticForms.LegendreTernary

/-!
# Robinson's lemmas on ternary quadratic forms

J. Robinson's definition of `ℤ` in `ℚ` (*J. Symbolic Logic* 14 (1949), Theorem 3.1) rests on four
lemmas about rational representations by ternary quadratic forms (pp. 107–108). Capital letters
denote rationals and small letters integers, and `(k / p)` is the Legendre symbol.

* `Rat.Robinson.lemma_one_only_if`: for a prime `p ≡ 3 (mod 4)`, if `X ^ 2 + Y ^ 2 - p Z ^ 2`
  represents a nonzero rational `M`, then `M` is not of the form `p k S ^ 2` with `(k / p) = 1`
  nor `k S ^ 2` with `k ≡ p (mod 8)`. This is the "only if" half of Lemma 1.
* `Rat.Robinson.lemma_two_only_if`: for odd primes `p ≡ 1 (mod 4)` and `q` with `(q / p) = -1`,
  if `X ^ 2 + q Y ^ 2 - p Z ^ 2` represents a nonzero rational `M`, then `M` is not of the form
  `p k S ^ 2` with `(k / p) = -1` nor `q k S ^ 2` with `(k / q) = -1`. This is the "only if" half
  of Lemma 2.
* `Rat.Robinson.lemma_three` (Lemma 3): for a prime `p ≡ 3 (mod 4)`,
  `2 + p M ^ 2 + p Z ^ 2 = X ^ 2 + Y ^ 2` is solvable in rationals exactly when the denominator of
  `M` is odd and prime to `p`.
* `Rat.Robinson.lemma_four` (Lemma 4): for odd primes `p ≡ 1 (mod 4)` and `q` with
  `(q / p) = -1`, `2 + p q M ^ 2 + p Z ^ 2 = X ^ 2 + q Y ^ 2` is solvable in rationals exactly
  when the denominator of `M` is prime to `p` and `q`.
* `Rat.Robinson.exists_sq_add_mul_sq_sub_mul_sq_eq`: `X ^ 2 + a Y ^ 2 - p Z ^ 2` represents every
  positive integer `m` prime to `a` and `p` with `m ≡ 2 (mod 4)`, or `m` odd and
  `(p / m) = (m / p)`; this is the case of the "if" halves of Lemmas 1 and 2 that Lemmas 3 and 4
  use.

The "only if" halves of Lemmas 1 and 2 are local obstructions, at `p` and `2`, and at `p` and `q`.
They are proved by descent: a solution in integers with the last variable nonzero would have all
its coordinates divisible by the prime. Robinson states Lemmas 1 and 2 as special cases of
Hasse's theorem on rational representations by quadratic forms; their "if" halves are cases of the
Hasse–Minkowski theorem for quaternary forms. For the representations that Lemmas 3 and 4 need,
the proof of `exists_sq_add_mul_sq_sub_mul_sq_eq` follows the classical reduction of the
quaternary case to the ternary one: an auxiliary prime `r` from Dirichlet's theorem
(`Nat.forall_exists_prime_gt_and_eq_mod`) is represented both by `X ^ 2 + a Y ^ 2` and by
`m₀ U ^ 2 + p V ^ 2`, where `m = t ^ 2 m₀` with `m₀` squarefree, by Legendre's theorem
(`Int.exists_ternary_eq_zero_iff`), and quadratic reciprocity for Jacobi symbols makes the
congruence conditions compatible.

## References

* J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, Lemmas 1–4, pp. 107–108, and the notation, p. 106.
-/

public section

namespace Rat.Robinson

/-! ### Clearing denominators -/

private theorem exists_int_eq_mul_of_den_dvd (X : ℚ) {D : ℕ} (h : X.den ∣ D) :
    ∃ x : ℤ, (x : ℚ) = X * D := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨X.num * a, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- Four rationals become integers after multiplication by one positive integer. -/
private theorem exists_common_den (X Y Z S : ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ x y z s : ℤ, (x : ℚ) = X * D ∧ (y : ℚ) = Y * D ∧ (z : ℚ) = Z * D ∧
      (s : ℚ) = S * D := by
  refine ⟨X.den * Y.den * Z.den * S.den, by positivity, ?_⟩
  obtain ⟨x, hx⟩ := exists_int_eq_mul_of_den_dvd X (D := X.den * Y.den * Z.den * S.den)
    ⟨Y.den * Z.den * S.den, by ring⟩
  obtain ⟨y, hy⟩ := exists_int_eq_mul_of_den_dvd Y (D := X.den * Y.den * Z.den * S.den)
    ⟨X.den * Z.den * S.den, by ring⟩
  obtain ⟨z, hz⟩ := exists_int_eq_mul_of_den_dvd Z (D := X.den * Y.den * Z.den * S.den)
    ⟨X.den * Y.den * S.den, by ring⟩
  obtain ⟨s, hs⟩ := exists_int_eq_mul_of_den_dvd S (D := X.den * Y.den * Z.den * S.den)
    ⟨X.den * Y.den * Z.den, by ring⟩
  exact ⟨x, y, z, s, hx, hy, hz, hs⟩

/-- An integer divisible by every power of an integer `ℓ ≥ 2` is `0`. -/
private theorem eq_zero_of_forall_pow_dvd {ℓ : ℕ} (hℓ : 1 < ℓ) {s : ℤ}
    (h : ∀ n : ℕ, (ℓ : ℤ) ^ n ∣ s) : s = 0 := by
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h s.natAbs) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self hℓ

/-! ### Local obstructions by descent -/

/-- Descent at an odd prime `ℓ`: if `α` and `β` are quadratic non-residues modulo `ℓ` and `ℓ`
does not divide `c`, then `x ^ 2 - α y ^ 2 = ℓ c (z ^ 2 - β s ^ 2)` forces `s = 0`. -/
private theorem eq_zero_of_sq_sub_mul_sq_eq {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α β c : ℤ}
    (hα : legendreSym ℓ α = -1) (hβ : legendreSym ℓ β = -1) (hc : ¬(ℓ : ℤ) ∣ c) {x y z s : ℤ}
    (h : x ^ 2 - α * y ^ 2 = ℓ * c * (z ^ 2 - β * s ^ 2)) : s = 0 := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
  have hℓ0 : (ℓ : ℤ) ≠ 0 := hp.ne_zero
  refine eq_zero_of_forall_pow_dvd hℓ.out.one_lt fun n => ?_
  induction n generalizing x y z s with
  | zero => exact one_dvd _
  | succ n ih =>
    obtain ⟨⟨x₁, rfl⟩, ⟨y₁, rfl⟩⟩ := legendreSym.prime_dvd_of_eq_neg_one hα
      (x := x) (y := y) ⟨c * (z ^ 2 - β * s ^ 2), by rw [h]; ring⟩
    have h₁ : (ℓ : ℤ) * (x₁ ^ 2 - α * y₁ ^ 2) = c * (z ^ 2 - β * s ^ 2) := by
      apply mul_left_cancel₀ hℓ0
      linear_combination h
    have hdvd : (ℓ : ℤ) ∣ z ^ 2 - β * s ^ 2 :=
      (hp.dvd_or_dvd ⟨_, h₁.symm⟩).resolve_left hc
    obtain ⟨⟨z₁, rfl⟩, ⟨s₁, rfl⟩⟩ := legendreSym.prime_dvd_of_eq_neg_one hβ hdvd
    have h₂ : x₁ ^ 2 - α * y₁ ^ 2 = ℓ * c * (z₁ ^ 2 - β * s₁ ^ 2) := by
      apply mul_left_cancel₀ hℓ0
      linear_combination h₁
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h₂)

/-- The residue of a square modulo `8`, with the parity of the root. -/
private theorem sq_zmod_eight (x : ℤ) :
    ((x : ZMod 8) ^ 2 = 1 ∧ Odd x) ∨ (((x : ZMod 8) ^ 2 = 0 ∨ (x : ZMod 8) ^ 2 = 4) ∧ Even x) := by
  have hx : ((x % 8 : ℤ) : ZMod 8) = x := ZMod.intCast_mod x 8
  have h0 : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
  have h8 : x % 8 < 8 := Int.emod_lt_of_pos x (by norm_num)
  rw [← hx, Int.odd_iff, Int.even_iff]
  have e2 : x % 2 = x % 8 % 2 := (Int.emod_emod_of_dvd x (by norm_num)).symm
  rw [e2]
  interval_cases x % 8 <;> decide

/-- Descent at `2`: if `p ≡ 3 (mod 4)` and `k ≡ p (mod 8)`, then
`x ^ 2 + y ^ 2 - p z ^ 2 = k s ^ 2` forces `s = 0`. -/
private theorem eq_zero_of_sq_add_sq_sub_mul_sq_eq_two {p k : ℤ} (hp : p % 4 = 3)
    (hk : k ≡ p [ZMOD 8]) {x y z s : ℤ} (h : x ^ 2 + y ^ 2 - p * z ^ 2 = k * s ^ 2) : s = 0 := by
  have key : ∀ P ∈ ({3, 7} : Finset (ZMod 8)), ∀ X ∈ ({0, 1, 4} : Finset (ZMod 8)),
      ∀ Y ∈ ({0, 1, 4} : Finset (ZMod 8)), ∀ Z ∈ ({0, 1, 4} : Finset (ZMod 8)),
      ∀ S ∈ ({0, 1, 4} : Finset (ZMod 8)), X + Y - P * Z = P * S →
        X ≠ 1 ∧ Y ≠ 1 ∧ Z ≠ 1 ∧ S ≠ 1 := by decide
  have hP : (p : ZMod 8) ∈ ({3, 7} : Finset (ZMod 8)) := by
    have hx : ((p % 8 : ℤ) : ZMod 8) = p := ZMod.intCast_mod p 8
    have h37 : p % 8 = 3 ∨ p % 8 = 7 := by omega
    rw [← hx]
    rcases h37 with h37 | h37 <;> rw [h37] <;> decide
  have hk8 : (k : ZMod 8) = p := (ZMod.intCast_eq_intCast_iff k p 8).mpr hk
  have hsq : ∀ w : ℤ, (w : ZMod 8) ^ 2 ∈ ({0, 1, 4} : Finset (ZMod 8)) ∧
      ((w : ZMod 8) ^ 2 ≠ 1 → Even w) := by
    intro w
    rcases sq_zmod_eight w with ⟨h1, -⟩ | ⟨h1 | h1, hw⟩
    · exact ⟨by simp [h1], fun h => absurd h1 h⟩
    · exact ⟨by simp [h1], fun _ => hw⟩
    · exact ⟨by simp [h1], fun _ => hw⟩
  refine eq_zero_of_forall_pow_dvd (ℓ := 2) one_lt_two fun n => ?_
  induction n generalizing x y z s with
  | zero => exact one_dvd _
  | succ n ih =>
    have hcast : ((x : ZMod 8) ^ 2) + (y : ZMod 8) ^ 2 - (p : ZMod 8) * (z : ZMod 8) ^ 2 =
        (p : ZMod 8) * (s : ZMod 8) ^ 2 := by
      have h8 := congrArg (Int.cast : ℤ → ZMod 8) h
      push_cast at h8
      rw [hk8] at h8
      exact h8
    obtain ⟨h1, h2, h3, h4⟩ := key _ hP _ (hsq x).1 _ (hsq y).1 _ (hsq z).1 _ (hsq s).1 hcast
    obtain ⟨x₁, rfl⟩ := ((hsq x).2 h1).two_dvd
    obtain ⟨y₁, rfl⟩ := ((hsq y).2 h2).two_dvd
    obtain ⟨z₁, rfl⟩ := ((hsq z).2 h3).two_dvd
    obtain ⟨s₁, rfl⟩ := ((hsq s).2 h4).two_dvd
    have h' : x₁ ^ 2 + y₁ ^ 2 - p * z₁ ^ 2 = k * s₁ ^ 2 := by
      apply mul_left_cancel₀ (four_ne_zero : (4 : ℤ) ≠ 0)
      linear_combination h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h')

/-- A rational solution of `X ^ 2 + a Y ^ 2 - b Z ^ 2 = c S ^ 2` with `S ≠ 0` gives an integral
one with `s ≠ 0`. -/
private theorem exists_int_solution {a b c : ℤ} {X Y Z S : ℚ}
    (h : X ^ 2 + a * Y ^ 2 - b * Z ^ 2 = c * S ^ 2) (hS : S ≠ 0) :
    ∃ x y z s : ℤ, s ≠ 0 ∧ x ^ 2 + a * y ^ 2 - b * z ^ 2 = c * s ^ 2 := by
  obtain ⟨D, hD, x, y, z, s, hx, hy, hz, hs⟩ := exists_common_den X Y Z S
  refine ⟨x, y, z, s, ?_, ?_⟩
  · rintro rfl
    have : S * D = 0 := by rw [← hs]; simp
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hS h0
    · exact (Nat.cast_ne_zero.mpr hD.ne') h0
  · have : (x : ℚ) ^ 2 + a * (y : ℚ) ^ 2 - b * (z : ℚ) ^ 2 = c * (s : ℚ) ^ 2 := by
      rw [hx, hy, hz, hs]
      linear_combination (D : ℚ) ^ 2 * h
    exact_mod_cast this

private theorem legendreSym_neg_one_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    legendreSym p (-1) = -1 := by
  rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_mod_four, hp]
  rfl

private theorem legendreSym_neg_one_of_mod_four_eq_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    legendreSym p (-1) = 1 := by
  rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_mod_four, hp]
  rfl

private theorem not_dvd_unit {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {c : ℤ} (hc : c = 1 ∨ c = -1) :
    ¬(ℓ : ℤ) ∣ c := by
  intro h
  have h1 : (ℓ : ℤ) ∣ 1 := by
    rcases hc with rfl | rfl
    · exact h
    · exact (dvd_neg.mp h)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hℓ.out.one_lt.ne' (by exact_mod_cast this)

/-! ### Robinson's Lemmas 1 and 2: the local conditions -/

/-- **Robinson's Lemma 1, necessity of the conditions.** Let `p` be a prime with
`p ≡ 3 (mod 4)` and let `M` be a nonzero rational number. If `X ^ 2 + Y ^ 2 - p Z ^ 2 = M` has a
solution in rational numbers `X, Y, Z`, then `M` is of neither of the forms `p k S ^ 2` with
`(k / p) = 1` and `k S ^ 2` with `k ≡ p (mod 8)`, where `k` is an integer and `S` a rational
number.

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 1, p. 107, states: "If `p` is a prime `≡ 3 (mod 4)` then `X² + Y² − pZ²` represents a
nonzero rational number `M`, if and only if `M` is not of the form `pk·S²` with `(k/p) = 1` or
`k·S²` with `k ≡ p (mod 8)`." Capital letters denote rationals and small letters integers
(p. 106). This theorem is the "only if" half: the conditions are the obstructions at `p` and at
`2`, proved here by descent. The converse is a case of the Hasse–Minkowski theorem for
representations by ternary forms; the special case of positive integers prime to `p` used in
Lemma 3 is `exists_sq_add_mul_sq_sub_mul_sq_eq`. -/
theorem lemma_one_only_if {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {M : ℚ} (hM : M ≠ 0)
    (h : ∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - p * Z ^ 2 = M) :
    (¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = 1) ∧
      ¬∃ (k : ℤ) (S : ℚ), M = k * S ^ 2 ∧ k ≡ p [ZMOD 8] := by
  obtain ⟨X, Y, Z, hXYZ⟩ := h
  constructor
  · rintro ⟨k, S, rfl, hk⟩
    have hS : S ≠ 0 := by rintro rfl; simp at hM
    obtain ⟨x, y, z, s, hs, hint⟩ := exists_int_solution (a := 1) (b := p) (c := p * k)
      (X := X) (Y := Y) (Z := Z) (S := S) (by push_cast; linear_combination hXYZ) hS
    have hneg := legendreSym_neg_one_of_mod_four_eq_three hp
    refine hs (eq_zero_of_sq_sub_mul_sq_eq (ℓ := p) (α := -1) (β := -k) (c := 1) hneg ?_
      (not_dvd_unit (Or.inl rfl)) (x := x) (y := y) (z := z) (s := s) (by linear_combination hint))
    rw [neg_eq_neg_one_mul, legendreSym.mul, hneg, hk]
    norm_num
  · rintro ⟨k, S, rfl, hk⟩
    have hS : S ≠ 0 := by rintro rfl; simp at hM
    obtain ⟨x, y, z, s, hs, hint⟩ := exists_int_solution (a := 1) (b := p) (c := k)
      (X := X) (Y := Y) (Z := Z) (S := S) (by push_cast; linear_combination hXYZ) hS
    exact hs (eq_zero_of_sq_add_sq_sub_mul_sq_eq_two (p := p) (by omega) hk
      (x := x) (y := y) (z := z) (s := s) (by linear_combination hint))

/-- **Robinson's Lemma 2, necessity of the conditions.** Let `p` and `q` be odd primes with
`p ≡ 1 (mod 4)` and `(q / p) = -1`, and let `M` be a nonzero rational number. If
`X ^ 2 + q Y ^ 2 - p Z ^ 2 = M` has a solution in rational numbers `X, Y, Z`, then `M` is of
neither of the forms `p k S ^ 2` with `(k / p) = -1` and `q k S ^ 2` with `(k / q) = -1`, where
`k` is an integer and `S` a rational number. (That `p` is odd follows from `p ≡ 1 (mod 4)`.)

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 2, p. 108, states: "If `p` and `q` are odd primes with `p ≡ 1 (mod 4)` and `(q/p) = −1`,
then `X² + qY² − pZ²` represents a nonzero rational number `M` if and only if `M` is not of the
form `pk·S²` with `(k/p) = −1` or `qk·S²` with `(k/q) = −1`." Capital letters denote rationals and
small letters integers (p. 106). This theorem is the "only if" half: the conditions are the
obstructions at `p` and at `q`, proved here by descent, with quadratic reciprocity for
`(p / q) = (q / p)`. The converse is a case of the Hasse–Minkowski theorem for representations by
ternary forms; the special case of positive integers prime to `p` and `q` used in Lemma 4 is
`exists_sq_add_mul_sq_sub_mul_sq_eq`. -/
theorem lemma_two_only_if {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1) (hq : q ≠ 2)
    (hqp : legendreSym p q = -1) {M : ℚ} (hM : M ≠ 0)
    (h : ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = M) :
    (¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = -1) ∧
      ¬∃ (k : ℤ) (S : ℚ), M = q * k * S ^ 2 ∧ legendreSym q k = -1 := by
  obtain ⟨X, Y, Z, hXYZ⟩ := h
  have hneg := legendreSym_neg_one_of_mod_four_eq_one hp
  constructor
  · rintro ⟨k, S, rfl, hk⟩
    have hS : S ≠ 0 := by rintro rfl; simp at hM
    obtain ⟨x, y, z, s, hs, hint⟩ := exists_int_solution (a := q) (b := p) (c := p * k)
      (X := X) (Y := Y) (Z := Z) (S := S) (by push_cast; linear_combination hXYZ) hS
    refine hs (eq_zero_of_sq_sub_mul_sq_eq (ℓ := p) (α := -q) (β := -k) (c := 1) ?_ ?_
      (not_dvd_unit (Or.inl rfl)) (x := x) (y := y) (z := z) (s := s) (by linear_combination hint))
    · rw [neg_eq_neg_one_mul, legendreSym.mul, hneg, hqp]
      norm_num
    · rw [neg_eq_neg_one_mul, legendreSym.mul, hneg, hk]
      norm_num
  · rintro ⟨k, S, rfl, hk⟩
    have hS : S ≠ 0 := by rintro rfl; simp at hM
    obtain ⟨x, y, z, s, hs, hint⟩ := exists_int_solution (a := q) (b := p) (c := q * k)
      (X := X) (Y := Y) (Z := Z) (S := S) (by push_cast; linear_combination hXYZ) hS
    have hpq : legendreSym q p = -1 := by
      rw [legendreSym.quadratic_reciprocity_one_mod_four hp hq, hqp]
    exact hs (eq_zero_of_sq_sub_mul_sq_eq (ℓ := q) (α := p) (β := k) (c := -1) hpq hk
      (not_dvd_unit (Or.inr rfl)) (x := x) (y := z) (z := y) (s := s) (by linear_combination hint))

/-! ### Representations by `X ^ 2 + a Y ^ 2 - p Z ^ 2`, from Legendre's theorem and Dirichlet's
theorem -/

private theorem jacobiSym_congr_left {x y b : ℕ} (h : x ≡ y [MOD b]) :
    jacobiSym x b = jacobiSym y b := by
  rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod]
  exact congrArg (fun n : ℕ => jacobiSym (n : ℤ) b) h

/-- A quadratic residue modulo a prime `r` is a square modulo `r`, as an integral congruence. -/
private theorem exists_sq_modEq_of_legendreSym_eq_one {r : ℕ} [Fact r.Prime] {A : ℤ}
    (h : legendreSym r A = 1) : ∃ x : ℤ, x ^ 2 ≡ A [ZMOD r] := by
  have hA : (A : ZMod r) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff r A).mpr h0] at h
    exact zero_ne_one h
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff r hA).mp h
  refine ⟨(y.val : ℤ), (ZMod.intCast_eq_intCast_iff _ _ r).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val, hy]
  ring

/-- Legendre's theorem for `A x ^ 2 + B y ^ 2 = r z ^ 2`, with `A, B` positive and `r` prime,
in the form used below: the congruence conditions give a solution with `z ≠ 0`. -/
private theorem exists_of_legendre {A B r : ℕ} (hA : 0 < A) (hB : 0 < B) (hr : r.Prime)
    (hA' : Squarefree A) (hB' : Squarefree B) (hAB : A.Coprime B) (hAr : A.Coprime r)
    (hBr : B.Coprime r) (h1 : ∃ x : ℤ, x ^ 2 ≡ -(A * B) [ZMOD r])
    (h2 : ∃ x : ℤ, x ^ 2 ≡ A * r [ZMOD B]) (h3 : ∃ x : ℤ, x ^ 2 ≡ B * r [ZMOD A]) :
    ∃ x y z : ℤ, z ≠ 0 ∧ A * x ^ 2 + B * y ^ 2 = r * z ^ 2 := by
  have hr' : Squarefree (-(r : ℤ)) :=
    (Int.prime_iff_natAbs_prime.mpr (by simpa using hr)).squarefree
  have hAi : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBi : (B : ℤ) ≠ 0 := by exact_mod_cast hB.ne'
  have hri : -(r : ℤ) ≠ 0 := by simpa using hr.ne_zero
  have hiff := Int.exists_ternary_eq_zero_iff hAi hBi hri (Int.squarefree_natCast.mpr hA')
    (Int.squarefree_natCast.mpr hB') hr' (Nat.Coprime.isCoprime hAB)
    (Nat.Coprime.isCoprime hBr).neg_right (Nat.Coprime.isCoprime hAr).neg_right
    (fun h => by have h3 := h.2.2; have h4 : (0 : ℤ) < r := (by exact_mod_cast hr.pos); omega)
    (fun h => by have := h.1; omega)
  obtain ⟨x, y, z, hne, h⟩ := hiff.mpr ⟨by
      obtain ⟨x, hx⟩ := h1
      exact ⟨x, Int.modEq_neg.mpr hx⟩, by
      obtain ⟨x, hx⟩ := h2
      exact ⟨x, by simpa using hx⟩, by
      obtain ⟨x, hx⟩ := h3
      exact ⟨x, by simpa using hx⟩⟩
  refine ⟨x, y, z, ?_, by linear_combination h⟩
  rintro rfl
  have hA0 : (0 : ℤ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℤ) < B := by exact_mod_cast hB
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact hne ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hx,
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hy, rfl⟩

/-- `p v ^ 2 = r w ^ 2` has no solution with `w ≠ 0` for distinct primes `p` and `r`: the
exponent of `p` is odd on the left and even on the right. -/
private theorem ne_of_mul_sq_eq {p r : ℕ} [hp : Fact p.Prime] (hr : r.Prime) (hpr : p ≠ r)
    {v w : ℤ} (hw : w ≠ 0) : (p : ℤ) * v ^ 2 ≠ r * w ^ 2 := by
  intro h
  have hv : v ≠ 0 := by
    rintro rfl
    have : (r : ℤ) * w ^ 2 ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne_zero) (pow_ne_zero 2 hw)
    exact this (by rw [← h]; ring)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hpr' : ¬(p : ℤ) ∣ r := by
    rw [Int.natCast_dvd_natCast]
    exact fun hd => hpr ((Nat.prime_dvd_prime_iff_eq hp.out hr).mp hd)
  have := congrArg (padicValInt p) h
  rw [padicValInt.mul hp0 (pow_ne_zero 2 hv), padicValInt.mul hr0 (pow_ne_zero 2 hw), sq, sq,
    padicValInt.mul hv hv, padicValInt.mul hw hw, padicValInt.self hp.out.one_lt,
    padicValInt.eq_zero_of_not_dvd hpr'] at this
  omega

/-- The case of a squarefree positive integer `m₀ = 2 ^ e m₁`: once the residue `c₈` of an
auxiliary prime modulo `8` makes the sign `χ₈(c₈) ^ e (p / m₁) (m₀ / p)` equal to `1`,
`X ^ 2 + a Y ^ 2 - p Z ^ 2` represents `m₀`. A prime `r ≡ 1 (mod a)`, `r ≡ m₀ (mod p)`,
`r ≡ p (mod m₁)`, `r ≡ c₈ (mod 8)` (Dirichlet's theorem) is represented by `X ^ 2 + a Y ^ 2` and by
`m₀ U ^ 2 + p V ^ 2` (Legendre's theorem twice). -/
private theorem exists_rep_of_squarefree {a p m₀ m₁ e c : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (ha0 : 0 < a) (ha : Squarefree a) (ha2 : Odd a) (hap : a.Coprime p) (ham₀ : a.Coprime m₀)
    (hm₀0 : 0 < m₀) (hm₀ : Squarefree m₀) (hpm₀ : ¬p ∣ m₀) (hm₁ : Odd m₁) (he1 : e ≤ 1)
    (he : m₀ = 2 ^ e * m₁) (hc : c % 4 = 1) (hc8 : c < 8)
    (hσ : ZMod.χ₈ (c : ZMod 8) ^ e * jacobiSym p m₁ * jacobiSym m₀ p = 1) :
    ∃ X Y Z : ℚ, X ^ 2 + a * Y ^ 2 - p * Z ^ 2 = m₀ := by
  have hp := hpf.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hm₁m₀ : m₁ ∣ m₀ := ⟨2 ^ e, by rw [he, mul_comm]⟩
  have hpm₀' : p.Coprime m₀ := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm₀
  have ham₁ : a.Coprime m₁ := ham₀.coprime_dvd_right hm₁m₀
  have hpm₁ : p.Coprime m₁ := hpm₀'.coprime_dvd_right hm₁m₀
  have h8 : ∀ {n : ℕ}, Odd n → n.Coprime 8 := fun hn =>
    (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hn)
  -- the residue class of the auxiliary prime
  obtain ⟨R₁, hR₁a, hR₁p⟩ := Nat.chineseRemainder hap 1 m₀
  obtain ⟨R₂, hR₂ap, hR₂m⟩ := Nat.chineseRemainder (Nat.Coprime.mul_left ham₁ hpm₁) R₁ p
  obtain ⟨R, hRapm, hR8⟩ := Nat.chineseRemainder
    (h8 (Odd.mul (Odd.mul ha2 hpodd) hm₁)) R₂ c
  set L := a * p * m₁ * 8 with hL
  have hL0 : L ≠ 0 := by
    have := hp.pos; have := hm₁.pos; positivity
  have : NeZero L := ⟨hL0⟩
  have hRa : R ≡ 1 [MOD a] :=
    ((hRapm.of_mul_right m₁).of_mul_right p).trans (hR₂ap.of_mul_right p) |>.trans hR₁a
  have hRp : R ≡ m₀ [MOD p] :=
    ((hRapm.of_mul_right m₁).of_mul_left a).trans (hR₂ap.of_mul_left a) |>.trans hR₁p
  have hRm : R ≡ p [MOD m₁] := (hRapm.of_mul_left (a * p)).trans hR₂m
  have hc8' : Nat.Coprime c 8 := by
    rcases (by omega : c = 1 ∨ c = 5) with rfl | rfl <;> decide
  have hunit : IsUnit (R : ZMod L) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
    · rw [Nat.Coprime, hRa.gcd_eq]; simp
    · rw [Nat.Coprime, hRp.gcd_eq]; exact hpm₀'.symm
    · rw [Nat.Coprime, hRm.gcd_eq]; exact hpm₁
    · rw [Nat.Coprime, hR8.gcd_eq]; exact hc8'
  obtain ⟨r, hrN, hr, hrR⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (p + m₀ + a)
  have : Fact r.Prime := ⟨hr⟩
  have hrL : r ≡ R [MOD L] := (ZMod.natCast_eq_natCast_iff r R L).mp hrR
  have hra : r ≡ 1 [MOD a] :=
    (((hrL.of_mul_right 8).of_mul_right m₁).of_mul_right p).trans hRa
  have hrp : r ≡ m₀ [MOD p] :=
    (((hrL.of_mul_right 8).of_mul_right m₁).of_mul_left a).trans hRp
  have hrm : r ≡ p [MOD m₁] := ((hrL.of_mul_right 8).of_mul_left (a * p)).trans hRm
  have hr8 : r ≡ c [MOD 8] := (hrL.of_mul_left (a * p * m₁)).trans hR8
  have hr8' : r % 8 = c := by rw [hr8, Nat.mod_eq_of_lt hc8]
  have hr4 : r % 4 = 1 := by omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hrp' : p ≠ r := by omega
  have hra' : a.Coprime r := by
    rw [Nat.coprime_comm, Nat.Coprime, hra.gcd_eq]; simp
  have hrm₀ : m₀.Coprime r := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hr).mpr fun hd => by
      have := Nat.le_of_dvd hm₀0 hd; omega
  have hpr : p.Coprime r := (Nat.coprime_primes hp hr).mpr hrp'
  have hχ₄ : legendreSym r (-1) = 1 := legendreSym_neg_one_of_mod_four_eq_one hr4
  -- `r` is represented by `X ^ 2 + a Y ^ 2`
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_of_legendre (A := 1) (B := a) (r := r) one_pos ha0 hr
    squarefree_one ha (Nat.coprime_one_left a) (Nat.coprime_one_left r) hra'
    (by
      refine exists_sq_modEq_of_legendreSym_eq_one ?_
      rw [Nat.cast_one, one_mul, neg_eq_neg_one_mul, legendreSym.mul, hχ₄, one_mul,
        jacobiSym.legendreSym.to_jacobiSym, jacobiSym.quadratic_reciprocity_one_mod_four' ha2 hr4,
        jacobiSym_congr_left hra, Nat.cast_one, jacobiSym.one_left])
    ⟨1, by
      have := (Int.natCast_modEq_iff.mpr hra).symm
      simpa using this⟩
    ⟨0, Int.modEq_one⟩
  -- `r` is represented by `m₀ U ^ 2 + p V ^ 2`
  have hrm₀' : r ≡ p [MOD m₀] := by
    rw [he]
    refine (Nat.modEq_and_modEq_iff_modEq_mul
      (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm₁))).mp ⟨?_, hrm⟩
    interval_cases e
    · exact Nat.modEq_one
    · rw [pow_one, Nat.ModEq, Nat.odd_iff.mp hrodd, Nat.odd_iff.mp hpodd]
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre (A := m₀) (B := p) (r := r) hm₀0 hp.pos hr
    hm₀ hp.prime.squarefree hpm₀'.symm hrm₀ hpr
    (by
      refine exists_sq_modEq_of_legendreSym_eq_one ?_
      have hrp_sym : legendreSym r p = jacobiSym m₀ p := by
        rw [← legendreSym.quadratic_reciprocity_one_mod_four hr4 hp2, legendreSym.mod,
          ← Int.natCast_mod, hrp, Int.natCast_mod, ← legendreSym.mod,
          jacobiSym.legendreSym.to_jacobiSym]
      have hrm_sym : legendreSym r m₀ = ZMod.χ₈ (c : ZMod 8) ^ e * jacobiSym p m₁ := by
        rw [jacobiSym.legendreSym.to_jacobiSym, he, Nat.cast_mul, jacobiSym.mul_left,
          Nat.cast_pow, jacobiSym.pow_left, Nat.cast_ofNat, jacobiSym.at_two hrodd,
          ZMod.χ₈_nat_mod_eight, hr8', jacobiSym.quadratic_reciprocity_one_mod_four' hm₁ hr4,
          jacobiSym_congr_left hrm]
      rw [neg_eq_neg_one_mul, legendreSym.mul, legendreSym.mul, hχ₄, hrp_sym, hrm_sym]
      linear_combination hσ)
    ⟨m₀, by
      have := Int.natCast_modEq_iff.mpr hrp
      calc (m₀ : ℤ) ^ 2 = m₀ * m₀ := sq _
        _ ≡ m₀ * r [ZMOD p] := this.symm.mul_left _⟩
    ⟨p, by
      have := Int.natCast_modEq_iff.mpr hrm₀'
      calc (p : ℤ) ^ 2 = p * p := sq _
        _ ≡ p * r [ZMOD m₀] := this.symm.mul_left _⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact ne_of_mul_sq_eq hr hrp' hw (v := v) (by linear_combination huvw)
  refine ⟨x * w / (z * u), y * w / (z * u), v / u, ?_⟩
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have h1 : ((x : ℚ)) ^ 2 + a * (y : ℚ) ^ 2 = r * (z : ℚ) ^ 2 := by
    exact_mod_cast (by linear_combination hxyz : x ^ 2 + (a : ℤ) * y ^ 2 = r * z ^ 2)
  have h2 : (m₀ : ℚ) * (u : ℚ) ^ 2 + p * (v : ℚ) ^ 2 = r * (w : ℚ) ^ 2 := by
    exact_mod_cast huvw
  field_simp
  linear_combination (w : ℚ) ^ 2 * h1 - (z : ℚ) ^ 2 * h2

/-- **Rational representations by `X ^ 2 + a Y ^ 2 - p Z ^ 2`.** Let `p` be an odd prime, `a` an
odd squarefree positive integer prime to `p`, and `m` a positive integer prime to `a` and to `p`,
with `m ≡ 2 (mod 4)`, or `m` odd with `(p / m) = (m / p)` (Jacobi symbols). Then
`X ^ 2 + a Y ^ 2 - p Z ^ 2 = m` has a solution in rational numbers `X, Y, Z`.

This is the case of Hasse's theorem behind the "if" halves of J. Robinson's Lemmas 3 and 4
(*J. Symbolic Logic* 14 (1949), p. 108), where `m = 2 d ^ 2 + p n ^ 2` with `a = 1`, and
`m = 2 d ^ 2 + p q n ^ 2` with `a = q`. Robinson derives these from Lemmas 1 and 2, special
cases of Hasse's theorem on rational representations by quadratic forms. Here the proof follows
the classical reduction of the four-variable Hasse–Minkowski theorem to the ternary case. Write
`m = t ^ 2 m₀` with `m₀` squarefree and take a prime `r` (Dirichlet's theorem) with
`r ≡ 1 (mod a)`, `r ≡ m₀ (mod p)`, `r ≡ p` modulo the odd part of `m₀` and `r ≡ 1 (mod 4)`, whose
class modulo `8` fixes the sign `(2 / r)`. Legendre's theorem (`Int.exists_ternary_eq_zero_iff`)
then solves `X ^ 2 + a Y ^ 2 = r` and `m₀ U ^ 2 + p V ^ 2 = r` in rationals. -/
theorem exists_sq_add_mul_sq_sub_mul_sq_eq {a p m : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (ha : Squarefree a) (ha2 : Odd a) (hap : a.Coprime p) (ham : a.Coprime m) (hm : 0 < m)
    (hpm : ¬p ∣ m) (h2 : m % 4 = 2 ∨ (Odd m ∧ jacobiSym p m = jacobiSym m p)) :
    ∃ X Y Z : ℚ, X ^ 2 + a * Y ^ 2 - p * Z ^ 2 = m := by
  have hp := hpf.out
  obtain ⟨m₀, t, hm₀0, ht0, htm, hsq⟩ := Nat.sq_mul_squarefree_of_pos hm
  have hm₀m : m₀ ∣ m := ⟨t ^ 2, by rw [← htm, mul_comm]⟩
  have htm' : t ∣ m := ⟨t * m₀, by rw [← htm]; ring⟩
  have ham₀ : a.Coprime m₀ := ham.coprime_dvd_right hm₀m
  have hpm₀ : ¬p ∣ m₀ := fun h => hpm (h.trans hm₀m)
  have hpm₀' : p.Coprime m₀ := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm₀
  have hpt : p.Coprime t := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpm (h.trans htm')
  have ha0 : 0 < a := ha2.pos
  suffices H : ∃ X Y Z : ℚ, X ^ 2 + a * Y ^ 2 - p * Z ^ 2 = m₀ by
    obtain ⟨X, Y, Z, h⟩ := H
    refine ⟨t * X, t * Y, t * Z, ?_⟩
    have : (m : ℚ) = t ^ 2 * m₀ := by exact_mod_cast htm.symm
    rw [this]
    linear_combination (t : ℚ) ^ 2 * h
  have hJ0 : ∀ {x y : ℕ}, x.Coprime y → jacobiSym x y = 1 ∨ jacobiSym x y = -1 := fun h =>
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact h)
  rcases h2 with h2 | ⟨hodd, hJ⟩
  · -- `m ≡ 2 (mod 4)`: `m₀ = 2 m₁` with `m₁` odd
    have ht : Odd t := by
      rcases Nat.even_or_odd t with ⟨k, rfl⟩ | h
      · exfalso
        have : 4 ∣ m := ⟨k ^ 2 * m₀, by rw [← htm]; ring⟩
        omega
      · exact h
    obtain ⟨m₁, hm₁⟩ : Even m₀ := by
      rcases Nat.even_or_odd m₀ with h | h
      · exact h
      · exfalso
        have : Odd m := htm ▸ (ht.pow).mul h
        rw [Nat.odd_iff] at this
        omega
    have hm₁o : Odd m₁ := by
      rcases Nat.even_or_odd m₁ with ⟨k, rfl⟩ | h
      · exfalso
        exact absurd (hsq 2 ⟨k, by omega⟩) (by decide)
      · exact h
    have he : m₀ = 2 ^ 1 * m₁ := by omega
    have hσ : jacobiSym p m₁ * jacobiSym m₀ p = 1 ∨ jacobiSym p m₁ * jacobiSym m₀ p = -1 := by
      rcases hJ0 (hpm₀'.coprime_dvd_right ⟨2, by omega⟩ : p.Coprime m₁) with h | h <;>
        rcases hJ0 hpm₀'.symm with h' | h' <;> simp [h, h']
    rcases hσ with hσ | hσ
    · exact exists_rep_of_squarefree (c := 1) hp2 ha0 ha ha2 hap ham₀ hm₀0 hsq hpm₀ hm₁o
        le_rfl he rfl (by norm_num) (by rw [pow_one, mul_assoc, hσ]; decide)
    · exact exists_rep_of_squarefree (c := 5) hp2 ha0 ha ha2 hap ham₀ hm₀0 hsq hpm₀ hm₁o
        le_rfl he rfl (by norm_num) (by
          rw [pow_one, mul_assoc, hσ]
          have : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
          rw [this]; norm_num)
  · -- `m` odd: `m₀` odd
    have hm₀o : Odd m₀ := hodd.of_dvd_nat hm₀m
    have hpt2 : jacobiSym p (t ^ 2) = 1 := by
      have : NeZero t := ⟨ht0.ne'⟩
      rw [sq, jacobiSym.mul_right, ← sq]
      exact jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hpt)
    have htp2 : jacobiSym ((t : ℤ) ^ 2) p = 1 :=
      jacobiSym.sq_one' (by rw [Int.gcd_natCast_natCast]; exact hpt.symm)
    have hJ' : jacobiSym p m₀ = jacobiSym m₀ p := by
      have : NeZero m₀ := ⟨hm₀0.ne'⟩
      have : NeZero (t ^ 2) := ⟨by positivity⟩
      rw [← htm, jacobiSym.mul_right, hpt2, one_mul, Nat.cast_mul, jacobiSym.mul_left,
        Nat.cast_pow, htp2, one_mul] at hJ
      exact hJ
    refine exists_rep_of_squarefree (e := 0) (m₁ := m₀) (c := 1) hp2 ha0 ha ha2 hap ham₀ hm₀0
      hsq hpm₀ hm₀o (Nat.zero_le _) (by ring) rfl (by norm_num) ?_
    rw [pow_zero, one_mul, hJ', ← sq]
    exact jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hpm₀'.symm)

/-! ### Robinson's Lemmas 3 and 4 -/

/-- Clearing the denominator `d` of `M`: solvability of `2 + C M ^ 2 + b Z ^ 2 = X ^ 2 + a Y ^ 2`
is the rational representation of `d ^ 2 (2 + C M ^ 2)` by `X ^ 2 + a Y ^ 2 - b Z ^ 2`. -/
private theorem exists_iff_exists_scaled {a b C M d : ℚ} (hd : d ≠ 0) :
    (∃ X Y Z : ℚ, 2 + C * M ^ 2 + b * Z ^ 2 = X ^ 2 + a * Y ^ 2) ↔
      ∃ X Y Z : ℚ, X ^ 2 + a * Y ^ 2 - b * Z ^ 2 = d ^ 2 * (2 + C * M ^ 2) := by
  constructor
  · rintro ⟨X, Y, Z, h⟩
    exact ⟨d * X, d * Y, d * Z, by linear_combination (-d ^ 2) * h⟩
  · rintro ⟨X, Y, Z, h⟩
    refine ⟨X / d, Y / d, Z / d, ?_⟩
    field_simp
    linear_combination -h

/-- `d ^ 2 (2 + C M ^ 2) = 2 d ^ 2 + C n ^ 2` for `M = n / d` in lowest terms. -/
private theorem den_sq_mul_eq (C M : ℚ) :
    (M.den : ℚ) ^ 2 * (2 + C * M ^ 2) = 2 * M.den ^ 2 + C * (M.num.natAbs : ℚ) ^ 2 := by
  have h1 : (M.num.natAbs : ℚ) ^ 2 = (M.num : ℚ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [h1, ← Rat.mul_den_eq_num]
  ring

/-- **Robinson's Lemma 3.** Let `p` be a prime with `p ≡ 3 (mod 4)` and let `M` be a rational
number. Then `2 + p M ^ 2 + p Z ^ 2 = X ^ 2 + Y ^ 2` has a solution in rational numbers `X, Y, Z`
if and only if the denominator of `M` in lowest terms is odd and prime to `p`.

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 3, p. 108: "If `p` is a prime `≡ 3 (mod 4)` then `2 + pM² + pZ² = X² + Y²` has a solution
for `X, Y`, and `Z` if and only if the denominator of `M` in lowest terms is odd and prime to `p`."
Capital letters denote rationals (p. 106). With `M = n / d` in lowest terms and
`m = 2 d ^ 2 + p n ^ 2`, the equation is solvable exactly when `X ^ 2 + Y ^ 2 - p Z ^ 2`
represents `m`. If `p ∣ d` or `2 ∣ d`, then `m` is of one of the forms that Robinson's Lemma 1
excludes (`lemma_one_only_if`). If `d` is odd and prime to `p`, then `m ≡ 1, 2 (mod 4)`, and `m` is
represented by `exists_sq_add_mul_sq_sub_mul_sq_eq`, which proves the needed case of the "if" half
of Lemma 1. -/
theorem lemma_three {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) (M : ℚ) :
    (∃ X Y Z : ℚ, 2 + p * M ^ 2 + p * Z ^ 2 = X ^ 2 + Y ^ 2) ↔ Odd M.den ∧ M.den.Coprime p := by
  have hpp := hpf.out
  have hp2 : p ≠ 2 := by omega
  set d := M.den with hd
  set n := M.num.natAbs with hn
  have hcop : n.Coprime d := M.reduced
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast M.den_nz
  set m : ℕ := 2 * d ^ 2 + p * n ^ 2 with hm
  have hmq : (d : ℚ) ^ 2 * (2 + p * M ^ 2) = m := by
    rw [den_sq_mul_eq, hm]; push_cast; ring
  have key : (∃ X Y Z : ℚ, 2 + p * M ^ 2 + p * Z ^ 2 = X ^ 2 + Y ^ 2) ↔
      ∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - p * Z ^ 2 = m := by
    have := exists_iff_exists_scaled (a := 1) (b := p) (C := p) (M := M) hd0
    simp only [one_mul] at this
    rw [this, hmq]
  have hm0 : 0 < m := by have := M.den_pos; positivity
  rw [key]
  constructor
  · intro hrep
    have hmne : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
    have h1 := lemma_one_only_if hp hmne hrep
    refine ⟨?_, ?_⟩
    · by_contra hodd
      obtain ⟨s, hs⟩ : Even d := Nat.not_odd_iff_even.mp hodd
      have hn2 : Odd n := by
        rcases Nat.even_or_odd n with ⟨i, hi⟩ | h
        · exfalso
          have := Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.coprime_dvd_left (show 2 ∣ n from ⟨i, by omega⟩) hcop)
            (show 2 ∣ d from ⟨s, by omega⟩)
          omega
        · exact h
      refine h1.2 ⟨m, 1, by simp, ?_⟩
      have hZ : (((m : ℤ)) : ZMod 8) = ((p : ℤ) : ZMod 8) → (m : ℤ) ≡ p [ZMOD 8] := fun h => by
        have := (ZMod.intCast_eq_intCast_iff (m : ℤ) p 8).mp h
        exact_mod_cast this
      refine hZ ?_
      have hsq := sq_zmod_eight (n : ℤ)
      rcases hsq with ⟨hsq, -⟩ | ⟨-, hev⟩
      · rw [hm, hs]
        push_cast
        have h8 : (8 : ZMod 8) = 0 := rfl
        have hn' : ((n : ℤ) : ZMod 8) ^ 2 = 1 := hsq
        push_cast at hn'
        rw [hn']
        linear_combination (s : ZMod 8) ^ 2 * h8
      · exact absurd (by exact_mod_cast hev : Even n) (Nat.not_even_iff_odd.mpr hn2)
    · by_contra hdp
      have hpd : p ∣ d := by
        by_contra h
        exact hdp ((Nat.Prime.coprime_iff_not_dvd hpp).mpr h).symm
      obtain ⟨r, hr⟩ := hpd
      have hpn : ¬p ∣ n := fun h => hpp.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hcop) ⟨r, hr⟩)
      refine h1.1 ⟨2 * p * r ^ 2 + n ^ 2, 1, ?_, ?_⟩
      · rw [hm, hr]; push_cast; ring
      · have hmod : ((2 * p * r ^ 2 + n ^ 2 : ℤ)) % p = ((n : ℤ) ^ 2) % p := by
          rw [show (2 * p * r ^ 2 + n ^ 2 : ℤ) = n ^ 2 + p * (2 * r ^ 2) by ring,
            Int.add_mul_emod_self_left]
        rw [legendreSym.mod, hmod, ← legendreSym.mod]
        refine legendreSym.sq_one' p ?_
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]
        exact hpn
  · rintro ⟨hodd, hdp⟩
    have hpm : ¬p ∣ m := by
      intro h
      have h' : p ∣ 2 * d ^ 2 := (Nat.dvd_add_left (dvd_mul_right p _)).mp h
      rcases (Nat.Prime.dvd_mul hpp).mp h' with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2)
      · exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hdp.symm (hpp.dvd_of_dvd_pow h2)
    obtain ⟨j, hj⟩ := hodd
    have h2 : m % 4 = 2 ∨ (Odd m ∧ jacobiSym p m = jacobiSym m p) := by
      rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨i, hi⟩
      · left
        have : m = 4 * (2 * j ^ 2 + 2 * j + p * i ^ 2) + 2 := by rw [hm, hj, hi]; ring
        omega
      · right
        obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
        have hm4 : m = 4 * (2 * j ^ 2 + 2 * j + (4 * k + 3) * (i ^ 2 + i) + k + 1) + 1 := by
          rw [hm, hj, hi, hk]; ring
        have hm4' : m % 4 = 1 := by omega
        exact ⟨Nat.odd_iff.mpr (by omega), (jacobiSym.quadratic_reciprocity_one_mod_four hm4'
          (hpp.odd_of_ne_two hp2)).symm⟩
    have := exists_sq_add_mul_sq_sub_mul_sq_eq (a := 1) (p := p) (m := m) hp2 squarefree_one
      odd_one (Nat.coprime_one_left _) (Nat.coprime_one_left _) hm0 hpm h2
    simpa using this

/-- **Robinson's Lemma 4.** Let `p` and `q` be odd primes with `p ≡ 1 (mod 4)` and
`(q / p) = -1`, and let `M` be a rational number. Then `2 + p q M ^ 2 + p Z ^ 2 = X ^ 2 + q Y ^ 2`
has a solution in rational numbers `X, Y, Z` if and only if the denominator of `M` in lowest terms
is prime to `p` and to `q`. (That `p` is odd follows from `p ≡ 1 (mod 4)`.)

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 4, p. 108: "If `p` and `q` are odd primes with `p ≡ 1 (mod 4)` and such that `(q/p) = −1`,
then `2 + pqM² + pZ² = X² + qY²` has a solution for `X, Y, Z` if and only if the denominator of `M`
in lowest terms is prime to `p` and `q`." Capital letters denote rationals (p. 106). With
`M = n / d` in lowest terms and `m = 2 d ^ 2 + p q n ^ 2`, the equation is solvable exactly when
`X ^ 2 + q Y ^ 2 - p Z ^ 2` represents `m`. If `p ∣ d` or `q ∣ d`, then `m` is of one of the forms
that Robinson's Lemma 2 excludes (`lemma_two_only_if`). If `d` is prime to `p` and `q`, then `m` is
represented by `exists_sq_add_mul_sq_sub_mul_sq_eq`, which proves the needed case of the "if" half
of Lemma 2. -/
theorem lemma_four {p q : ℕ} [hpf : Fact p.Prime] [hqf : Fact q.Prime] (hp : p % 4 = 1)
    (hq : q ≠ 2) (hqp : legendreSym p q = -1) (M : ℚ) :
    (∃ X Y Z : ℚ, 2 + p * q * M ^ 2 + p * Z ^ 2 = X ^ 2 + q * Y ^ 2) ↔
      M.den.Coprime p ∧ M.den.Coprime q := by
  have hpp := hpf.out
  have hqq := hqf.out
  have hp2 : p ≠ 2 := by omega
  have hpq : ¬p ∣ q := by
    intro h
    have : ((q : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]; exact h
    rw [(legendreSym.eq_zero_iff p q).mpr this] at hqp
    norm_num at hqp
  have hqp' : q.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpq).symm
  set d := M.den with hd
  set n := M.num.natAbs with hn
  have hcop : n.Coprime d := M.reduced
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast M.den_nz
  set m : ℕ := 2 * d ^ 2 + p * q * n ^ 2 with hm
  have hmq : (d : ℚ) ^ 2 * (2 + p * q * M ^ 2) = m := by
    rw [den_sq_mul_eq, hm]; push_cast; ring
  have key : (∃ X Y Z : ℚ, 2 + p * q * M ^ 2 + p * Z ^ 2 = X ^ 2 + q * Y ^ 2) ↔
      ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = m := by
    rw [exists_iff_exists_scaled (a := q) (b := p) (C := p * q) (M := M) hd0, hmq]
  have hm0 : 0 < m := by have := M.den_pos; positivity
  rw [key]
  -- a prime dividing `d` does not divide `n`
  have hndvd : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ∣ d → ¬(((n : ℤ)) : ZMod ℓ) = 0 := by
    intro ℓ hℓ hℓd h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓ.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hcop) hℓd)
  constructor
  · intro hrep
    have hmne : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
    have h2 := lemma_two_only_if hp hq hqp hmne hrep
    refine ⟨?_, ?_⟩
    · by_contra hdp
      have hpd : p ∣ d := by
        by_contra h
        exact hdp ((Nat.Prime.coprime_iff_not_dvd hpp).mpr h).symm
      obtain ⟨r, hr⟩ := hpd
      refine h2.1 ⟨2 * p * r ^ 2 + q * n ^ 2, 1, ?_, ?_⟩
      · rw [hm, hr]; push_cast; ring
      · have hmod : ((2 * p * r ^ 2 + q * n ^ 2 : ℤ)) % p = ((q : ℤ) * (n : ℤ) ^ 2) % p := by
          rw [show (2 * p * r ^ 2 + q * n ^ 2 : ℤ) = q * n ^ 2 + p * (2 * r ^ 2) by ring,
            Int.add_mul_emod_self_left]
        rw [legendreSym.mod, hmod, ← legendreSym.mod, legendreSym.mul, hqp,
          legendreSym.sq_one' p (hndvd hpp ⟨r, hr⟩)]
        norm_num
    · by_contra hdq
      have hqd : q ∣ d := by
        by_contra h
        exact hdq ((Nat.Prime.coprime_iff_not_dvd hqq).mpr h).symm
      obtain ⟨r, hr⟩ := hqd
      refine h2.2 ⟨2 * q * r ^ 2 + p * n ^ 2, 1, ?_, ?_⟩
      · rw [hm, hr]; push_cast; ring
      · have hmod : ((2 * q * r ^ 2 + p * n ^ 2 : ℤ)) % q = ((p : ℤ) * (n : ℤ) ^ 2) % q := by
          rw [show (2 * q * r ^ 2 + p * n ^ 2 : ℤ) = p * n ^ 2 + q * (2 * r ^ 2) by ring,
            Int.add_mul_emod_self_left]
        rw [legendreSym.mod, hmod, ← legendreSym.mod, legendreSym.mul,
          legendreSym.quadratic_reciprocity_one_mod_four hp hq, hqp,
          legendreSym.sq_one' q (hndvd hqq ⟨r, hr⟩)]
        norm_num
  · rintro ⟨hdp, hdq⟩
    have hnd : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ≠ 2 → d.Coprime ℓ → ℓ ∣ p * q * n ^ 2 → ¬ℓ ∣ m := by
      intro ℓ hℓ hℓ2 hdℓ hℓpq h
      have h' : ℓ ∣ 2 * d ^ 2 := (Nat.dvd_add_left hℓpq).mp h
      rcases (Nat.Prime.dvd_mul hℓ).mp h' with h2 | h2
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
      · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hdℓ.symm (hℓ.dvd_of_dvd_pow h2)
    have hpm : ¬p ∣ m := hnd hpp hp2 hdp ⟨q * n ^ 2, by ring⟩
    have hqm : ¬q ∣ m := hnd hqq hq hdq ⟨p * n ^ 2, by ring⟩
    have h2 : m % 4 = 2 ∨ (Odd m ∧ jacobiSym p m = jacobiSym m p) := by
      rcases Nat.even_or_odd m with hev | hodd
      · left
        obtain ⟨i, hi⟩ : Even n := by
          rcases Nat.even_or_odd n with h | h
          · exact h
          · exfalso
            have : Odd m := by
              rw [hm]
              exact Even.add_odd (even_two.mul_right _)
                ((hpp.odd_of_ne_two hp2).mul (hqq.odd_of_ne_two hq) |>.mul h.pow)
            exact (Nat.not_even_iff_odd.mpr this) hev
        obtain ⟨j, hj⟩ : Odd d := by
          rcases Nat.even_or_odd d with ⟨s, hs⟩ | h
          · exfalso
            have := Nat.Coprime.eq_one_of_dvd
              (Nat.Coprime.coprime_dvd_left (show 2 ∣ n from ⟨i, by omega⟩) hcop)
              (show 2 ∣ d from ⟨s, by omega⟩)
            omega
          · exact h
        have : m = 4 * (2 * j ^ 2 + 2 * j + p * q * i ^ 2) + 2 := by rw [hm, hj, hi]; ring
        omega
      · exact Or.inr ⟨hodd, jacobiSym.quadratic_reciprocity_one_mod_four hp hodd⟩
    exact exists_sq_add_mul_sq_sub_mul_sq_eq (a := q) (p := p) (m := m) hp2 hqq.prime.squarefree
      (hqq.odd_of_ne_two hq) hqp' ((Nat.Prime.coprime_iff_not_dvd hqq).mpr hqm) hm0 hpm h2

end Rat.Robinson

end
