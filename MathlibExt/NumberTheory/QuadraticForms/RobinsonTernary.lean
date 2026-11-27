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

* `Rat.Robinson.lemma_one` (Lemma 1): for a prime `p ≡ 3 (mod 4)`, `X ^ 2 + Y ^ 2 - p Z ^ 2`
  represents a nonzero rational `M` exactly when `M` is not of the form `p k S ^ 2` with
  `(k / p) = 1` nor `k S ^ 2` with `k ≡ p (mod 8)`; its "only if" half is
  `Rat.Robinson.lemma_one_only_if`.
* `Rat.Robinson.lemma_two` (Lemma 2): for odd primes `p ≡ 1 (mod 4)` and `q` with
  `(q / p) = -1`, `X ^ 2 + q Y ^ 2 - p Z ^ 2` represents a nonzero rational `M` exactly when `M`
  is not of the form `p k S ^ 2` with `(k / p) = -1` nor `q k S ^ 2` with `(k / q) = -1`; its
  "only if" half is `Rat.Robinson.lemma_two_only_if`.
* `Rat.Robinson.lemma_three` (Lemma 3): for a prime `p ≡ 3 (mod 4)`,
  `2 + p M ^ 2 + p Z ^ 2 = X ^ 2 + Y ^ 2` is solvable in rationals exactly when the denominator of
  `M` is odd and prime to `p`.
* `Rat.Robinson.lemma_four` (Lemma 4): for odd primes `p ≡ 1 (mod 4)` and `q` with
  `(q / p) = -1`, `2 + p q M ^ 2 + p Z ^ 2 = X ^ 2 + q Y ^ 2` is solvable in rationals exactly
  when the denominator of `M` is prime to `p` and `q`.
* `Rat.Robinson.exists_sq_add_mul_sq_sub_mul_sq_eq`: for an odd prime `p` and an odd squarefree
  `a` prime to `p`, `X ^ 2 + a Y ^ 2 - p Z ^ 2` represents every positive integer `m` prime to `a`
  and `p` with `m ≡ 2 (mod 4)`, or `m` odd and `(p / m) = (m / p)`; this is the case of the "if"
  halves of Lemmas 1 and 2 that Lemmas 3 and 4 use.

The "only if" halves of Lemmas 1 and 2 are local obstructions, at `p` and `2`, and at `p` and `q`.
They are proved by descent: a solution in integers with the last variable nonzero would have all
its coordinates divisible by the prime. Robinson states Lemmas 1 and 2 as special cases of
Hasse's theorem on rational representations by quadratic forms; their "if" halves are cases of the
Hasse–Minkowski theorem for quaternary forms. They are proved here by the classical reduction of
the quaternary case to the ternary one: an auxiliary number `T`, a prime `r` from Dirichlet's
theorem (`Nat.forall_exists_prime_gt_and_eq_mod`) times a fixed factor, is represented both by
`X ^ 2 + a Y ^ 2` and by a binary form attached to the target, by Legendre's theorem
(`Int.exists_ternary_eq_zero_iff`), and quadratic reciprocity for Jacobi symbols makes the
congruence conditions compatible. Lemmas 3 and 4 use only `exists_sq_add_mul_sq_sub_mul_sq_eq`.

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
`2`, proved here by descent. The whole lemma is `lemma_one`. -/
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
`(p / q) = (q / p)`. The whole lemma is `lemma_two`. -/
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

/-! ### Tools for the "if" halves of Lemmas 1 and 2 -/

/-- An auxiliary prime in three residue classes modulo pairwise coprime moduli (Dirichlet's
theorem and the Chinese remainder theorem). -/
private theorem exists_prime_modEq {n₁ n₂ n₃ c₁ c₂ c₃ : ℕ} (h12 : n₁.Coprime n₂)
    (h13 : n₁.Coprime n₃) (h23 : n₂.Coprime n₃) (hc₁ : c₁.Coprime n₁) (hc₂ : c₂.Coprime n₂)
    (hc₃ : c₃.Coprime n₃) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (N : ℕ) :
    ∃ r : ℕ, r.Prime ∧ N < r ∧ r ≡ c₁ [MOD n₁] ∧ r ≡ c₂ [MOD n₂] ∧ r ≡ c₃ [MOD n₃] := by
  obtain ⟨R₁, hR₁a, hR₁b⟩ := Nat.chineseRemainder h12 c₁ c₂
  obtain ⟨R, hR₁, hR₃⟩ := Nat.chineseRemainder (Nat.Coprime.mul_left h13 h23) R₁ c₃
  have hRa : R ≡ c₁ [MOD n₁] := (hR₁.of_mul_right n₂).trans hR₁a
  have hRb : R ≡ c₂ [MOD n₂] := (hR₁.of_mul_left n₁).trans hR₁b
  have : NeZero (n₁ * n₂ * n₃) := ⟨by positivity⟩
  have hunit : IsUnit (R : ZMod (n₁ * n₂ * n₃)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
    · rw [Nat.Coprime, hRa.gcd_eq]; exact hc₁
    · rw [Nat.Coprime, hRb.gcd_eq]; exact hc₂
    · rw [Nat.Coprime, hR₃.gcd_eq]; exact hc₃
  obtain ⟨r, hrN, hr, hrR⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit N
  have hrL : r ≡ R [MOD n₁ * n₂ * n₃] := (ZMod.natCast_eq_natCast_iff r R _).mp hrR
  exact ⟨r, hr, hrN, ((hrL.of_mul_right n₃).of_mul_right n₂).trans hRa,
    ((hrL.of_mul_right n₃).of_mul_left n₁).trans hRb, (hrL.of_mul_left (n₁ * n₂)).trans hR₃⟩

/-- Squares modulo coprime moduli combine into a square modulo their product. -/
private theorem exists_sq_modEq_mul {c m n : ℤ} (h : IsCoprime m n)
    (hm : ∃ x : ℤ, x ^ 2 ≡ c [ZMOD m]) (hn : ∃ y : ℤ, y ^ 2 ≡ c [ZMOD n]) :
    ∃ z : ℤ, z ^ 2 ≡ c [ZMOD m * n] := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := hn
  have hgcd : m.natAbs.Coprime n.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  obtain ⟨u, v, huv⟩ := h
  set z := x * (v * n) + y * (u * m) with hz
  refine ⟨z, (Int.modEq_and_modEq_iff_modEq_mul hgcd).mp ⟨?_, ?_⟩⟩
  · have : z ≡ x [ZMOD m] := by
      rw [Int.modEq_iff_dvd]; exact ⟨u * (x - y), by rw [hz]; linear_combination (-x) * huv⟩
    exact (this.pow 2).trans hx
  · have : z ≡ y [ZMOD n] := by
      rw [Int.modEq_iff_dvd]; exact ⟨v * (y - x), by rw [hz]; linear_combination (-y) * huv⟩
    exact (this.pow 2).trans hy

/-- Every integer is a square modulo `2`. -/
private theorem exists_sq_modEq_two (c : ℤ) : ∃ x : ℤ, x ^ 2 ≡ c [ZMOD 2] := by
  refine ⟨c, ?_⟩
  have h := (ZMod.intCast_eq_intCast_iff (c ^ 2) c 2).mp (by
    push_cast
    generalize (c : ZMod 2) = t
    revert t
    decide)
  exact_mod_cast h

/-- `c u ^ 2 = ℓ c' v ^ 2` forces `u = v = 0` when the prime `ℓ` divides neither `c` nor `c'`:
the exponent of `ℓ` is even on the left and odd on the right. -/
private theorem eq_zero_of_mul_sq_eq_mul_sq {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {c c' u v : ℤ}
    (hc : ¬(ℓ : ℤ) ∣ c) (hc' : ¬(ℓ : ℤ) ∣ c') (h : c * u ^ 2 = ℓ * c' * v ^ 2) :
    u = 0 ∧ v = 0 := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  have hc'0 : c' ≠ 0 := by rintro rfl; exact hc' (dvd_zero _)
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  by_cases hu : u = 0
  · subst hu
    refine ⟨rfl, ?_⟩
    have : (ℓ : ℤ) * c' * v ^ 2 = 0 := by rw [← h]; ring
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
      ((mul_eq_zero.mp this).resolve_left (mul_ne_zero hℓ0 hc'0))
  · exfalso
    have hv : v ≠ 0 := by
      rintro rfl
      have : c * u ^ 2 = 0 := by rw [h]; ring
      exact (mul_ne_zero hc0 (pow_ne_zero 2 hu)) this
    have := congrArg (padicValInt ℓ) h
    rw [padicValInt.mul hc0 (pow_ne_zero 2 hu), padicValInt.mul (mul_ne_zero hℓ0 hc'0)
      (pow_ne_zero 2 hv), padicValInt.mul hℓ0 hc'0, sq, sq, padicValInt.mul hu hu,
      padicValInt.mul hv hv, padicValInt.self hℓ.out.one_lt, padicValInt.eq_zero_of_not_dvd hc,
      padicValInt.eq_zero_of_not_dvd hc'] at this
    omega

/-- Legendre's theorem for `A x ^ 2 + B y ^ 2 = T z ^ 2` with `B, T > 0` and `A x ^ 2 + B y ^ 2`
anisotropic: the congruence conditions give a solution with `z ≠ 0`. -/
private theorem exists_of_legendre' {A B T : ℤ} (hA0 : A ≠ 0) (hB : 0 < B) (hT : 0 < T)
    (hA : Squarefree A) (hB' : Squarefree B) (hT' : Squarefree T) (hAB : IsCoprime A B)
    (hBT : IsCoprime B T) (hAT : IsCoprime A T)
    (haniso : ∀ x y : ℤ, A * x ^ 2 + B * y ^ 2 = 0 → x = 0 ∧ y = 0)
    (h1 : ∃ x : ℤ, x ^ 2 ≡ -(A * B) [ZMOD T]) (h2 : ∃ x : ℤ, x ^ 2 ≡ A * T [ZMOD B])
    (h3 : ∃ x : ℤ, x ^ 2 ≡ B * T [ZMOD A]) :
    ∃ x y z : ℤ, z ≠ 0 ∧ A * x ^ 2 + B * y ^ 2 = T * z ^ 2 := by
  have hiff := Int.exists_ternary_eq_zero_iff hA0 hB.ne' (neg_ne_zero.mpr hT.ne') hA hB'
    (by rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]; exact hT')
    hAB hBT.neg_right hAT.neg_right (fun h => by have := h.2.2; omega)
    (fun h => by have := h.2.1; omega)
  obtain ⟨x, y, z, hne, h⟩ := hiff.mpr ⟨by
      obtain ⟨x, hx⟩ := h1
      exact ⟨x, Int.modEq_neg.mpr hx⟩, by
      obtain ⟨x, hx⟩ := h2
      exact ⟨x, by simpa using hx⟩, by
      obtain ⟨x, hx⟩ := h3
      exact ⟨x, by simpa using hx⟩⟩
  refine ⟨x, y, z, ?_, by linear_combination h⟩
  rintro rfl
  obtain ⟨hx, hy⟩ := haniso x y (by linear_combination h)
  exact hne ⟨hx, hy, rfl⟩

/-- A nonzero rational number is `m₀ S ^ 2` with `m₀` a squarefree integer. -/
private theorem exists_squarefree_mul_sq {M : ℚ} (hM : M ≠ 0) :
    ∃ (m₀ : ℤ) (S : ℚ), Squarefree m₀ ∧ S ≠ 0 ∧ M = m₀ * S ^ 2 := by
  set N : ℤ := M.num * M.den with hN
  have hN0 : N ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hM) (by exact_mod_cast M.den_nz)
  obtain ⟨m, t, hm, ht, htm, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hN0)
  refine ⟨N.sign * m, t / M.den, ?_, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hN0, one_mul,
      Int.natAbs_natCast]
    exact hsq
  · exact div_ne_zero (by exact_mod_cast ht.ne') (by exact_mod_cast M.den_nz)
  · have hd : (M.den : ℚ) ≠ 0 := by exact_mod_cast M.den_nz
    have h1z : N = N.sign * ((t ^ 2 * m : ℕ) : ℤ) := by
      rw [htm]; exact (Int.sign_mul_natAbs N).symm
    have h1 : (N : ℚ) = N.sign * (t ^ 2 * m : ℕ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h1z
    have h2 : (N : ℚ) = M * M.den ^ 2 := by
      rw [hN]; push_cast; rw [← Rat.mul_den_eq_num]; ring
    field_simp
    rw [← h2, h1]
    push_cast
    ring

/-- Two representations of an auxiliary number `T` combine into a representation of `A`. -/
private theorem exists_of_combine {a κ A B T x y z u v w : ℤ} (hz : z ≠ 0) (hu : u ≠ 0)
    (h1 : x ^ 2 + a * y ^ 2 = T * z ^ 2) (h2 : A * u ^ 2 + B * v ^ 2 = κ * T * w ^ 2) :
    ∃ X Y Z : ℚ, (A : ℚ) = κ * (X ^ 2 + a * Y ^ 2) - B * Z ^ 2 := by
  refine ⟨x * w / (z * u), y * w / (z * u), v / u, ?_⟩
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have h1' : (x : ℚ) ^ 2 + a * (y : ℚ) ^ 2 = T * (z : ℚ) ^ 2 := by exact_mod_cast h1
  have h2' : (A : ℚ) * (u : ℚ) ^ 2 + B * (v : ℚ) ^ 2 = κ * T * (w : ℚ) ^ 2 := by
    exact_mod_cast h2
  field_simp
  linear_combination (z : ℚ) ^ 2 * h2' - κ * (w : ℚ) ^ 2 * h1'

/-! ### The "if" half of Lemma 1 -/

/-- A squarefree integer is `± 2 ^ e m₁` with `e ≤ 1` and `m₁` odd. -/
private theorem exists_two_pow_mul_odd {m₀ : ℤ} (hm₀ : Squarefree m₀) :
    ∃ e m₁ : ℕ, e ≤ 1 ∧ Odd m₁ ∧ m₀.natAbs = 2 ^ e * m₁ := by
  have hn : Squarefree m₀.natAbs := Int.squarefree_natAbs.mpr hm₀
  rcases Nat.even_or_odd m₀.natAbs with ⟨k, hk⟩ | h
  · refine ⟨1, k, le_rfl, ?_, by omega⟩
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | h
    · exact absurd (hn 2 ⟨j, by omega⟩) (by decide)
    · exact h
  · exact ⟨0, m₀.natAbs, Nat.zero_le _, h, by ring⟩

/-- For `r ≡ 1 (mod 4)`, the Jacobi symbol `(m / r)` depends only on `|m|`. -/
private theorem jacobiSym_eq_natAbs {m : ℤ} {r : ℕ} (hr : r % 4 = 1) :
    jacobiSym m r = jacobiSym m.natAbs r := by
  rcases Int.natAbs_eq m with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h]
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₄_nat_mod_four, hr]
    simp

/-- `(2 ^ e m₁ / r) = (2 / r) ^ e (m₁ / r)` for odd `r`. -/
private theorem jacobiSym_two_pow_mul {e m₁ r : ℕ} (hr : Odd r) :
    jacobiSym ((2 ^ e * m₁ : ℕ) : ℤ) r = ZMod.χ₈ (r : ZMod 8) ^ e * jacobiSym m₁ r := by
  rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left, Nat.cast_ofNat,
    jacobiSym.at_two hr]

/-- Quadratic reciprocity for a prime `p ≡ 3 (mod 4)` and an odd `m`. -/
private theorem jacobiSym_recip_three {p m : ℕ} (hp : p % 4 = 3) (hm : Odd m) :
    jacobiSym p m = (if m % 4 = 3 then -1 else 1) * jacobiSym m p := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with h | h
  · rw [ite_eq_right (by omega), one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h
      (Nat.odd_iff.mpr (by omega))]
  · rw [ite_eq_left h, jacobiSym.quadratic_reciprocity_three_mod_four hp h]; ring

/-- For a prime `p ≡ 3 (mod 4)`, `(m / p) = ± (|m| / p)`, with the sign of `m`. -/
private theorem jacobiSym_eq_sign_natAbs {m : ℤ} {p : ℕ} (hp : p % 4 = 3) :
    jacobiSym m p = (if m < 0 then -1 else 1) * jacobiSym m.natAbs p := by
  rcases lt_or_ge m 0 with h | h
  · rw [ite_eq_left h]
    have : m = -1 * (m.natAbs : ℤ) := by omega
    conv_lhs => rw [this]
    rw [jacobiSym.mul_left, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₄_nat_mod_four, hp]
    rfl
  · rw [ite_eq_right (not_lt.mpr h), one_mul]
    congr 1
    omega

/-- The natural residue of an integer modulo `n > 0`. -/
private theorem natRes_modEq (m : ℤ) {n : ℕ} (hn : 0 < n) :
    (((m % n).toNat : ℕ) : ℤ) ≡ m [ZMOD n] := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  exact Int.mod_modEq m n

/-- The natural residue modulo a prime `p` of an integer prime to `p` is prime to `p`. -/
private theorem natRes_coprime {p : ℕ} (hp : p.Prime) {m : ℤ} (h : ¬(p : ℤ) ∣ m) :
    ((m % p).toNat : ℕ).Coprime p := by
  have h0 : ((m % p).toNat : ℤ) = m % p :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero))
  refine ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => h ?_).symm
  have h1 : (p : ℤ) ∣ m % p := by rw [← h0]; exact Int.natCast_dvd_natCast.mpr hd
  have h2 := dvd_add (Int.mod_modEq m p).dvd h1
  simpa using h2

/-- An odd prime `r ≡ 1 (mod 4)` is a value of `x ^ 2 + y ^ 2` times a nonzero square. -/
private theorem exists_norm_one {r : ℕ} (hr : r.Prime) (hr4 : r % 4 = 1) :
    ∃ x y z : ℤ, z ≠ 0 ∧ x ^ 2 + 1 * y ^ 2 = r * z ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, y, z, hz, h⟩ := exists_of_legendre' (A := 1) (B := 1) (T := r) one_ne_zero one_pos
    (by exact_mod_cast hr.pos) squarefree_one squarefree_one
    (Int.squarefree_natCast.mpr hr.prime.squarefree) isCoprime_one_left isCoprime_one_left
    isCoprime_one_left (fun x y h => by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_eq_zero_iff (a := x),
        pow_eq_zero_iff (n := 2) (a := y) two_ne_zero])
    (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [mul_one, legendreSym_neg_one_of_mod_four_eq_one hr4]))
    ⟨0, Int.modEq_one⟩ ⟨0, Int.modEq_one⟩
  exact ⟨x, y, z, hz, by linear_combination h⟩

/-- An odd prime `r ≡ 1 (mod 4)`: `2 r` is a value of `x ^ 2 + y ^ 2` times a nonzero square. -/
private theorem exists_norm_two {r : ℕ} (hr : r.Prime) (hr4 : r % 4 = 1) :
    ∃ x y z : ℤ, z ≠ 0 ∧ x ^ 2 + 1 * y ^ 2 = (2 * r : ℤ) * z ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : IsCoprime (2 : ℤ) r := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have hsq : Squarefree (2 * r : ℤ) := by
    rw [← Int.squarefree_natAbs]
    have : (2 * (r : ℤ)).natAbs = 2 * r := by omega
    rw [this, Nat.squarefree_mul_iff]
    exact ⟨Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)), Nat.prime_two.prime.squarefree,
      hr.prime.squarefree⟩
  obtain ⟨x, y, z, hz, h⟩ := exists_of_legendre' (A := 1) (B := 1) (T := 2 * r) one_ne_zero
    one_pos (by have := hr.pos; omega) squarefree_one squarefree_one hsq isCoprime_one_left
    isCoprime_one_left isCoprime_one_left (fun x y h => by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_eq_zero_iff (a := x),
        pow_eq_zero_iff (n := 2) (a := y) two_ne_zero])
    (exists_sq_modEq_mul hr2 (exists_sq_modEq_two _) (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [mul_one, legendreSym_neg_one_of_mod_four_eq_one hr4])))
    ⟨0, Int.modEq_one⟩ ⟨0, Int.modEq_one⟩
  exact ⟨x, y, z, hz, by linear_combination h⟩

/-- A prime that does not divide an integer is coprime to it. -/
private theorem isCoprime_of_not_dvd {p : ℕ} (hp : p.Prime) {m : ℤ} (h : ¬(p : ℤ) ∣ m) :
    IsCoprime (p : ℤ) m := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h' => h (Int.ofNat_dvd_left.mpr h')

/-- A prime larger than `|m|` does not divide `m ≠ 0`. -/
private theorem not_dvd_of_lt {r : ℕ} {m : ℤ} (hm : m ≠ 0) (h : m.natAbs < r) : ¬(r : ℤ) ∣ m :=
  fun hd => by
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.ofNat_dvd_left.mp hd)
    omega

/-- From `r ≡ p` modulo `m₁` and modulo `2 ^ e` (`e ≤ 1`, both odd) to `r ≡ p` modulo
`m = ± 2 ^ e m₁`. -/
private theorem modEq_of_modEq_odd {r p e m₁ : ℕ} {m : ℤ} (he1 : e ≤ 1) (hm₁ : Odd m₁)
    (habs : m.natAbs = 2 ^ e * m₁) (hr : Odd r) (hp : Odd p) (h : r ≡ p [MOD m₁]) :
    (r : ℤ) ≡ p [ZMOD m] := by
  have h2 : r ≡ p [MOD 2 ^ e * m₁] := by
    refine (Nat.modEq_and_modEq_iff_modEq_mul
      (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm₁))).mp ⟨?_, h⟩
    interval_cases e
    · exact Nat.modEq_one
    · rw [pow_one, Nat.ModEq, Nat.odd_iff.mp hr, Nat.odd_iff.mp hp]
  rw [← habs] at h2
  have h3 := Int.natCast_modEq_iff.mpr h2
  rw [Int.modEq_iff_dvd] at h3 ⊢
  exact Int.natAbs_dvd.mp h3

/-- Case `p ∤ m₀` with `m₀` even or `m₀ ≡ 1 (mod 4)`: an auxiliary prime `r ≡ 1 (mod 4)`. -/
private theorem lemma_one_if_A1 {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) {m₀ : ℤ}
    {e m₁ : ℕ} (hm₀ : Squarefree m₀) (hpm : ¬(p : ℤ) ∣ m₀) (he1 : e ≤ 1) (hm₁ : Odd m₁)
    (habs : m₀.natAbs = 2 ^ e * m₁) (h4 : e = 1 ∨ m₀ % 4 = 1) :
    ∃ X Y Z : ℚ, (m₀ : ℚ) = 1 * (X ^ 2 + 1 * Y ^ 2) - p * Z ^ 2 := by
  have hpp := hpf.out
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hm₀0 : m₀ ≠ 0 := hm₀.ne_zero
  have hpm₁ : p.Coprime m₁ := (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h =>
    hpm (Int.ofNat_dvd_left.mpr (habs ▸ Dvd.dvd.mul_left h _))
  have hpm₀ : IsCoprime (p : ℤ) m₀ := isCoprime_of_not_dvd hpp hpm
  have hJ1 : jacobiSym p m₁ = 1 ∨ jacobiSym p m₁ = -1 :=
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact hpm₁)
  have hJ2 : jacobiSym m₀ p = 1 ∨ jacobiSym m₀ p = -1 :=
    jacobiSym.eq_one_or_neg_one (by
      have := Int.isCoprime_iff_gcd_eq_one.mp hpm₀.symm; exact this)
  -- the residue of `r` modulo `8`
  obtain ⟨c, hc4, hc8, hc⟩ : ∃ c : ℕ, c % 4 = 1 ∧ c < 8 ∧
      ZMod.χ₈ (c : ZMod 8) ^ e * jacobiSym p m₁ * jacobiSym m₀ p = 1 := by
    rcases h4 with rfl | h4
    · rcases hJ1 with h1 | h1 <;> rcases hJ2 with h2 | h2
      · exact ⟨1, rfl, by norm_num, by rw [h1, h2]; decide⟩
      · exact ⟨5, rfl, by norm_num, by rw [h1, h2]; decide⟩
      · exact ⟨5, rfl, by norm_num, by rw [h1, h2]; decide⟩
      · exact ⟨1, rfl, by norm_num, by rw [h1, h2]; decide⟩
    · refine ⟨1, rfl, by norm_num, ?_⟩
      have he : e = 0 := by
        by_contra he
        have : e = 1 := by omega
        subst this
        omega
      subst he
      rw [pow_zero, one_mul] at habs
      rw [pow_zero, one_mul, jacobiSym_recip_three hp hm₁, jacobiSym_eq_sign_natAbs (m := m₀) hp,
        habs]
      have hsq : jacobiSym m₁ p ^ 2 = 1 :=
        jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hpm₁.symm)
      rcases lt_or_ge m₀ 0 with hneg | hpos
      · rw [ite_eq_left hneg, ite_eq_left (by omega)]; linear_combination hsq
      · rw [ite_eq_right (not_lt.mpr hpos), ite_eq_right (by omega)]; linear_combination hsq
  -- the auxiliary prime
  have hc8' : Nat.Coprime c 8 := by
    rcases (by omega : c = 1 ∨ c = 5) with rfl | rfl <;> decide
  have hres : ((m₀ % p).toNat : ℕ).Coprime p := natRes_coprime hpp hpm
  obtain ⟨r, hr, hrN, hr8, hrp, hrm⟩ := exists_prime_modEq (n₁ := 8) (n₂ := p) (n₃ := m₁)
    (c₁ := c) (c₂ := (m₀ % p).toNat) (c₃ := p)
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hpodd)))
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hm₁))) hpm₁ hc8' hres hpm₁ (by norm_num)
    hpp.pos hm₁.pos (p + m₀.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hr8' : r % 8 = c := by rw [hr8, Nat.mod_eq_of_lt hc8]
  have hr4 : r % 4 = 1 := by omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hrpZ : (r : ℤ) ≡ m₀ [ZMOD p] :=
    (Int.natCast_modEq_iff.mpr hrp).trans (natRes_modEq m₀ hpp.pos)
  have hrm₀ : (r : ℤ) ≡ p [ZMOD m₀] := modEq_of_modEq_odd he1 hm₁ habs hrodd hpodd hrm
  have hpr : p ≠ r := by omega
  -- `r` is represented by `X ^ 2 + Y ^ 2`
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_one hr hr4
  -- `r` is represented by `m₀ U ^ 2 + p V ^ 2`
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := m₀) (B := p) (T := r) hm₀0
    (by exact_mod_cast hpp.pos) (by exact_mod_cast hr.pos) hm₀
    (Int.squarefree_natCast.mpr hpp.prime.squarefree)
    (Int.squarefree_natCast.mpr hr.prime.squarefree) hpm₀.symm
    (Nat.Coprime.isCoprime ((Nat.coprime_primes hpp hr).mpr hpr))
    (isCoprime_of_not_dvd hr (not_dvd_of_lt hm₀0 (by omega))).symm
    (fun x y h => eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := -m₀) (c' := 1)
      (fun h' => hpm (dvd_neg.mp h')) (not_dvd_unit (Or.inl rfl)) (by linear_combination -h))
    (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left,
        jacobiSym.mul_left, jacobiSym.at_neg_one hrodd, ZMod.χ₄_nat_mod_four, hr4,
        jacobiSym_eq_natAbs hr4, habs, jacobiSym_two_pow_mul hrodd, ZMod.χ₈_nat_mod_eight, hr8',
        jacobiSym.quadratic_reciprocity_one_mod_four' hm₁ hr4, jacobiSym_congr_left hrm,
        jacobiSym.quadratic_reciprocity_one_mod_four' hpodd hr4, jacobiSym.mod_left (r : ℤ),
        show (r : ℤ) % p = m₀ % p from hrpZ, ← jacobiSym.mod_left]
      have h1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide
      rw [h1]
      linear_combination hc))
    ⟨m₀, by
      calc m₀ ^ 2 = m₀ * m₀ := sq _
        _ ≡ m₀ * r [ZMOD p] := hrpZ.symm.mul_left _⟩
    ⟨p, by
      calc (p : ℤ) ^ 2 = p * p := sq _
        _ ≡ p * r [ZMOD m₀] := hrm₀.symm.mul_left _⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := r) (c' := 1)
      (by exact_mod_cast fun h => hpr ((Nat.prime_dvd_prime_iff_eq hpp hr).mp h))
      (not_dvd_unit (Or.inl rfl)) (u := w) (v := v) (by linear_combination -huvw)).1
  exact exists_of_combine (κ := 1) (A := m₀) (B := p) (T := r) (u := u) (v := v) (w := w) hz hu
    hxyz (by linear_combination huvw)

/-- `2 r` is squarefree for an odd prime `r`. -/
private theorem squarefree_two_mul_prime {r : ℕ} (hr : r.Prime) (hr2 : Odd r) :
    Squarefree (2 * r : ℤ) := by
  rw [← Int.squarefree_natAbs]
  have : (2 * (r : ℤ)).natAbs = 2 * r := by omega
  rw [this, Nat.squarefree_mul_iff]
  exact ⟨Nat.coprime_two_left.mpr hr2, Nat.prime_two.prime.squarefree, hr.prime.squarefree⟩

/-- Half of `m + 1` is invertible modulo an odd `m`. -/
private theorem half_coprime {m : ℕ} (hm : Odd m) : ((m + 1) / 2).Coprime m :=
  Nat.coprime_of_mul_modEq_one 2 (by
    have : (m + 1) / 2 * 2 = m + 1 := by obtain ⟨k, rfl⟩ := hm; omega
    rw [this, Nat.ModEq, Nat.add_mod_left])

/-- Case `p ∤ m₀`, `m₀ ≡ 3 (mod 4)`: the auxiliary number is `2 r`. -/
private theorem lemma_one_if_A2 {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) {m₀ : ℤ}
    {m₁ : ℕ} (hm₀ : Squarefree m₀) (hpm : ¬(p : ℤ) ∣ m₀) (hm₁ : Odd m₁)
    (habs : m₀.natAbs = m₁) (h4 : m₀ % 4 = 3) (h8 : ¬m₀ ≡ p [ZMOD 8]) :
    ∃ X Y Z : ℚ, (m₀ : ℚ) = 1 * (X ^ 2 + 1 * Y ^ 2) - p * Z ^ 2 := by
  have hpp := hpf.out
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hm₀0 : m₀ ≠ 0 := hm₀.ne_zero
  have hm₀odd : Odd m₀ := Int.odd_iff.mpr (by omega)
  have hpm₁ : p.Coprime m₁ := (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h =>
    hpm (Int.ofNat_dvd_left.mpr (habs ▸ h))
  have hpm₀ : IsCoprime (p : ℤ) m₀ := isCoprime_of_not_dvd hpp hpm
  set h₂ : ℕ := (p + 1) / 2 with hh₂
  have h₂p : 2 * h₂ = p + 1 := by obtain ⟨k, hk⟩ := hpodd; omega
  have hpmh : ¬(p : ℤ) ∣ m₀ * h₂ := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
    · exact hpm h
    · have := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp h); omega
  obtain ⟨r, hr, hrN, hr8, hrp, hrm⟩ := exists_prime_modEq (n₁ := 8) (n₂ := p) (n₃ := m₁)
    (c₁ := 1) (c₂ := ((m₀ * h₂) % p).toNat) (c₃ := p * ((m₁ + 1) / 2))
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hpodd)))
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hm₁))) hpm₁ (by norm_num)
    (natRes_coprime hpp hpmh) (Nat.Coprime.mul_left hpm₁ (half_coprime hm₁)) (by norm_num) hpp.pos
    hm₁.pos (p + m₀.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hr4 : r % 4 = 1 := by
    have : r % 8 = 1 := hr8
    omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hpr : p ≠ r := by omega
  -- `2 r ≡ m₀ (mod p)` and `2 r ≡ p (mod m₁)`
  have h2rp : (2 * r : ℤ) ≡ m₀ [ZMOD p] := by
    have h1 := (Int.natCast_modEq_iff.mpr hrp).trans (natRes_modEq (m₀ * h₂) hpp.pos)
    have h2 := h1.mul_left 2
    have h3 : (2 : ℤ) * (m₀ * h₂) = m₀ + p * m₀ := by
      have : (2 * h₂ : ℤ) = p + 1 := by exact_mod_cast h₂p
      linear_combination m₀ * this
    rw [h3] at h2
    exact h2.trans (Int.modEq_iff_dvd.mpr ⟨-m₀, by ring⟩)
  have h2rm : 2 * r ≡ p [MOD m₁] := by
    have h2 := hrm.mul_left 2
    have h3 : 2 * (p * ((m₁ + 1) / 2)) = p + m₁ * p := by
      have : 2 * ((m₁ + 1) / 2) = m₁ + 1 := by obtain ⟨k, rfl⟩ := hm₁; omega
      calc 2 * (p * ((m₁ + 1) / 2)) = p * (2 * ((m₁ + 1) / 2)) := by ring
        _ = p + m₁ * p := by rw [this]; ring
    rw [h3] at h2
    exact h2.trans (by rw [Nat.ModEq, Nat.add_mul_mod_self_left])
  have h2rm₀ : (2 * r : ℤ) ≡ p [ZMOD m₀] := by
    have h1 := Int.natCast_modEq_iff.mpr h2rm
    push_cast at h1
    rw [Int.modEq_iff_dvd] at h1 ⊢
    exact Int.natAbs_dvd.mp (habs ▸ h1)
  -- `2 r` is represented by `X ^ 2 + Y ^ 2`
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_two hr hr4
  -- `2 r` is represented by `m₀ U ^ 2 + p V ^ 2`
  have hrm₀ : IsCoprime m₀ (r : ℤ) :=
    (isCoprime_of_not_dvd hr (not_dvd_of_lt hm₀0 (by omega))).symm
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := m₀) (B := p) (T := 2 * r) hm₀0
    (by exact_mod_cast hpp.pos) (by have := hr.pos; omega) hm₀
    (Int.squarefree_natCast.mpr hpp.prime.squarefree) (squarefree_two_mul_prime hr hrodd)
    hpm₀.symm (IsCoprime.mul_right (Int.isCoprime_two_right.mpr (by exact_mod_cast hpodd))
      (Nat.Coprime.isCoprime ((Nat.coprime_primes hpp hr).mpr hpr)))
    (IsCoprime.mul_right (Int.isCoprime_two_right.mpr hm₀odd) hrm₀)
    (fun x y h => eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := -m₀) (c' := 1)
      (fun h' => hpm (dvd_neg.mp h')) (not_dvd_unit (Or.inl rfl)) (by linear_combination -h))
    (exists_sq_modEq_mul (Int.isCoprime_two_left.mpr (by exact_mod_cast hrodd))
      (exists_sq_modEq_two _) (exists_sq_modEq_of_legendreSym_eq_one (by
        have hJm : jacobiSym r m₁ = ZMod.χ₈ (m₁ : ZMod 8) * jacobiSym p m₁ := by
          have h1 := jacobiSym_congr_left h2rm
          rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_ofNat, jacobiSym.at_two hm₁] at h1
          rw [← h1, ← mul_assoc, ← sq]
          have : ZMod.χ₈ (m₁ : ZMod 8) ^ 2 = 1 := by
            rw [ZMod.χ₈_nat_mod_eight]
            rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm₁) with h | h <;>
              rcases (by omega : m₁ % 8 = 1 ∨ m₁ % 8 = 3 ∨ m₁ % 8 = 5 ∨ m₁ % 8 = 7) with
                h' | h' | h' | h' <;> rw [h'] <;> decide
          rw [this, one_mul]
        have hJp : jacobiSym r p = ZMod.χ₈ (p : ZMod 8) * jacobiSym m₀ p := by
          have h1 : jacobiSym (2 * r : ℤ) p = jacobiSym m₀ p := by
            rw [jacobiSym.mod_left, show (2 * r : ℤ) % p = m₀ % p from h2rp,
              ← jacobiSym.mod_left]
          rw [jacobiSym.mul_left, jacobiSym.at_two hpodd] at h1
          rw [← h1, ← mul_assoc, ← sq]
          have : ZMod.χ₈ (p : ZMod 8) ^ 2 = 1 := by
            rw [ZMod.χ₈_nat_mod_eight]
            rcases (by omega : p % 8 = 3 ∨ p % 8 = 7) with h' | h' <;> rw [h'] <;> decide
          rw [this, one_mul]
        have hsq : jacobiSym m₁ p ^ 2 = 1 :=
          jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hpm₁.symm)
        have hχ : ZMod.χ₈ (m₁ : ZMod 8) * ZMod.χ₈ (p : ZMod 8) = -1 := by
          rw [ZMod.χ₈_nat_mod_eight, ZMod.χ₈_nat_mod_eight p]
          have h8' : m₀ % 8 ≠ (p : ℤ) % 8 := h8
          rcases Int.natAbs_eq m₀ with he | he <;> rw [habs] at he <;>
            rcases (by omega : (m₁ % 8 = 3 ∧ p % 8 = 7) ∨ (m₁ % 8 = 7 ∧ p % 8 = 3) ∨
              (m₁ % 8 = 5 ∧ p % 8 = 7) ∨ (m₁ % 8 = 1 ∧ p % 8 = 3)) with
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
        have hsign : jacobiSym p m₁ * jacobiSym m₀ p = -1 := by
          rw [jacobiSym_recip_three hp hm₁, jacobiSym_eq_sign_natAbs (m := m₀) hp, habs]
          rcases lt_or_ge m₀ 0 with hneg | hpos
          · rw [ite_eq_left hneg, ite_eq_right (by omega)]; linear_combination -hsq
          · rw [ite_eq_right (not_lt.mpr hpos), ite_eq_left (by omega)]; linear_combination -hsq
        rw [jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left,
          jacobiSym.mul_left, jacobiSym.at_neg_one hrodd, ZMod.χ₄_nat_mod_four, hr4,
          jacobiSym_eq_natAbs hr4, habs, jacobiSym.quadratic_reciprocity_one_mod_four' hm₁ hr4,
          jacobiSym.quadratic_reciprocity_one_mod_four' hpodd hr4, hJm, hJp]
        have h1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide
        rw [h1]
        linear_combination (ZMod.χ₈ (m₁ : ZMod 8) * ZMod.χ₈ (p : ZMod 8)) * hsign - hχ)))
    ⟨m₀, by
      calc m₀ ^ 2 = m₀ * m₀ := sq _
        _ ≡ m₀ * (2 * r) [ZMOD p] := h2rp.symm.mul_left _⟩
    ⟨p, by
      calc (p : ℤ) ^ 2 = p * p := sq _
        _ ≡ p * (2 * r) [ZMOD m₀] := h2rm₀.symm.mul_left _⟩
  have hu : u ≠ 0 := by
    rintro rfl
    refine hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := 2 * r) (c' := 1) ?_
      (not_dvd_unit (Or.inl rfl)) (u := w) (v := v) (by linear_combination -huvw)).1
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
    · have := Int.le_of_dvd (by norm_num) h; omega
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hpp hr).mp (Int.natCast_dvd_natCast.mp h))
  exact exists_of_combine (κ := 1) (A := m₀) (B := p) (T := 2 * r) (u := u) (v := v) (w := w)
    hz hu hxyz (by linear_combination huvw)

/-- `p r` is squarefree for distinct primes `p`, `r`, and so is `p (2 r)` when both are odd. -/
private theorem squarefree_prime_mul {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    Squarefree (p * r : ℤ) := by
  rw [← Int.squarefree_natAbs]
  have : ((p : ℤ) * r).natAbs = p * r := by rw [Int.natAbs_mul]; simp
  rw [this, Nat.squarefree_mul_iff]
  exact ⟨(Nat.coprime_primes hp hr).mpr hpr, hp.prime.squarefree, hr.prime.squarefree⟩

private theorem squarefree_prime_mul_two_mul {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hp2 : Odd p) (hr2 : Odd r) : Squarefree (p * (2 * r) : ℤ) := by
  rw [← Int.squarefree_natAbs]
  have : ((p : ℤ) * (2 * r)).natAbs = p * (2 * r) := by
    rw [show ((p : ℤ) * (2 * r)) = ((p * (2 * r) : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  rw [this, Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
  exact ⟨Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hp2)
    ((Nat.coprime_primes hp hr).mpr hpr), hp.prime.squarefree, Nat.coprime_two_left.mpr hr2,
    Nat.prime_two.prime.squarefree, hr.prime.squarefree⟩

/-- `m x ^ 2 + y ^ 2` is anisotropic for a squarefree `m ≠ -1`. -/
private theorem aniso_one {m : ℤ} (hm : Squarefree m) (hm1 : m ≠ -1) (x y : ℤ)
    (h : m * x ^ 2 + 1 * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  rcases lt_or_ge m 0 with hneg | hpos
  · have h2 : 2 ≤ (-m).natAbs := by omega
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd (show (-m).natAbs ≠ 1 by omega)
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨c', hc'⟩ : (ℓ : ℤ) ∣ -m := Int.ofNat_dvd_left.mpr hℓd
    have hc'ℓ : ¬(ℓ : ℤ) ∣ c' := by
      rintro ⟨d, rfl⟩
      have : (ℓ : ℤ) * ℓ ∣ m := ⟨-d, by linear_combination -hc'⟩
      exact hℓ.one_lt.ne' (by
        have := Int.isUnit_iff_natAbs_eq.mp (hm (ℓ : ℤ) this)
        simpa using this)
    obtain ⟨hy, hx⟩ := eq_zero_of_mul_sq_eq_mul_sq (ℓ := ℓ) (c := 1) (c' := c') (u := y) (v := x)
      (not_dvd_unit (Or.inl rfl)) hc'ℓ (by linear_combination h + x ^ 2 * hc')
    exact ⟨hx, hy⟩
  · have hm0 : 0 < m := lt_of_le_of_ne hpos (Ne.symm hm.ne_zero)
    have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hx,
      pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hy⟩

/-- Case `m₀ = p m'` with `m'` even or `m' ≡ 3 (mod 4)`: the auxiliary number is `p r`. -/
private theorem lemma_one_if_B1 {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) {m' : ℤ}
    {e m₁ : ℕ} (hm' : Squarefree m') (hpm : ¬(p : ℤ) ∣ m') (hJ : legendreSym p m' = -1)
    (hm1 : m' ≠ -1) (he1 : e ≤ 1) (hm₁ : Odd m₁) (habs : m'.natAbs = 2 ^ e * m₁)
    (h4 : e = 1 ∨ m' % 4 = 3) :
    ∃ X Y Z : ℚ, (m' : ℚ) = p * (X ^ 2 + 1 * Y ^ 2) - 1 * Z ^ 2 := by
  have hpp := hpf.out
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hm0 : m' ≠ 0 := hm'.ne_zero
  have hpm₁ : p.Coprime m₁ := (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h =>
    hpm (Int.ofNat_dvd_left.mpr (habs ▸ Dvd.dvd.mul_left h _))
  have hJ' : jacobiSym m' p = -1 := by rw [← jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  have hJ1 : jacobiSym p m₁ = 1 ∨ jacobiSym p m₁ = -1 :=
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact hpm₁)
  obtain ⟨c, hc4, hc8, hc⟩ : ∃ c : ℕ, c % 4 = 1 ∧ c < 8 ∧
      ZMod.χ₈ (c : ZMod 8) ^ e * jacobiSym p m₁ = 1 := by
    rcases h4 with rfl | h4
    · rcases hJ1 with h1 | h1
      · exact ⟨1, rfl, by norm_num, by rw [h1]; decide⟩
      · exact ⟨5, rfl, by norm_num, by rw [h1]; decide⟩
    · refine ⟨1, rfl, by norm_num, ?_⟩
      have he : e = 0 := by
        by_contra he
        have : e = 1 := by omega
        subst this
        omega
      subst he
      rw [pow_zero, one_mul] at habs
      rw [pow_zero, one_mul, jacobiSym_recip_three hp hm₁]
      rw [jacobiSym_eq_sign_natAbs (m := m') hp, habs] at hJ'
      rcases lt_or_ge m' 0 with hneg | hpos
      · rw [ite_eq_left hneg] at hJ'; rw [ite_eq_right (by omega)]; linear_combination -hJ'
      · rw [ite_eq_right (not_lt.mpr hpos)] at hJ'; rw [ite_eq_left (by omega)]
        linear_combination -hJ'
  have hc8' : Nat.Coprime c 8 := by
    rcases (by omega : c = 1 ∨ c = 5) with rfl | rfl <;> decide
  obtain ⟨r, hr, hrN, hr8, hrm, -⟩ := exists_prime_modEq (n₁ := 8) (n₂ := m₁) (n₃ := 1)
    (c₁ := c) (c₂ := p) (c₃ := 0)
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hm₁))) (Nat.coprime_one_right _)
    (Nat.coprime_one_right _) hc8' hpm₁ (Nat.coprime_one_right _) (by norm_num) hm₁.pos one_pos
    (p + m'.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hr8' : r % 8 = c := by rw [hr8, Nat.mod_eq_of_lt hc8]
  have hr4 : r % 4 = 1 := by omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hpr : p ≠ r := by omega
  have hrm' : (r : ℤ) ≡ p [ZMOD m'] := modEq_of_modEq_odd he1 hm₁ habs hrodd hpodd hrm
  have hprC : IsCoprime (p : ℤ) r := Nat.Coprime.isCoprime ((Nat.coprime_primes hpp hr).mpr hpr)
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_one hr hr4
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := m') (B := 1) (T := p * r) hm0 one_pos
    (by have := hpp.pos; have := hr.pos; positivity) hm' squarefree_one
    (squarefree_prime_mul hpp hr hpr) isCoprime_one_right isCoprime_one_left
    (IsCoprime.mul_right (isCoprime_of_not_dvd hpp hpm).symm
      (isCoprime_of_not_dvd hr (not_dvd_of_lt hm0 (by omega))).symm)
    (aniso_one hm' hm1)
    (exists_sq_modEq_mul hprC
      (exists_sq_modEq_of_legendreSym_eq_one (by
        rw [mul_one, neg_eq_neg_one_mul, legendreSym.mul,
          legendreSym_neg_one_of_mod_four_eq_three hp, hJ]
        norm_num))
      (exists_sq_modEq_of_legendreSym_eq_one (by
        rw [mul_one, jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left,
          jacobiSym.at_neg_one hrodd, ZMod.χ₄_nat_mod_four, hr4, jacobiSym_eq_natAbs hr4, habs,
          jacobiSym_two_pow_mul hrodd, ZMod.χ₈_nat_mod_eight, hr8',
          jacobiSym.quadratic_reciprocity_one_mod_four' hm₁ hr4, jacobiSym_congr_left hrm]
        have h1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide
        rw [h1]
        linear_combination hc)))
    ⟨0, Int.modEq_one⟩
    ⟨p, by
      calc (p : ℤ) ^ 2 = p * p := sq _
        _ ≡ p * r [ZMOD m'] := hrm'.symm.mul_left _
        _ = 1 * (p * r) := by ring⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := 1) (c' := r) (u := v) (v := w)
      (not_dvd_unit (Or.inl rfl))
      (by exact_mod_cast fun h => hpr ((Nat.prime_dvd_prime_iff_eq hpp hr).mp h))
      (by linear_combination huvw)).2
  exact exists_of_combine (κ := p) (A := m') (B := 1) (T := r) (u := u) (v := v) (w := w) hz hu
    hxyz (by linear_combination huvw)

/-- Case `m₀ = p m'` with `m' ≡ 5 (mod 8)`: the auxiliary number is `2 p r`. -/
private theorem lemma_one_if_B2 {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) {m' : ℤ}
    {m₁ : ℕ} (hm' : Squarefree m') (hpm : ¬(p : ℤ) ∣ m') (hJ : legendreSym p m' = -1)
    (hm₁ : Odd m₁) (habs : m'.natAbs = m₁) (h8 : m' % 8 = 5) :
    ∃ X Y Z : ℚ, (m' : ℚ) = p * (X ^ 2 + 1 * Y ^ 2) - 1 * Z ^ 2 := by
  have hpp := hpf.out
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hm0 : m' ≠ 0 := hm'.ne_zero
  have hm'odd : Odd m' := Int.odd_iff.mpr (by omega)
  have hpm₁ : p.Coprime m₁ := (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h =>
    hpm (Int.ofNat_dvd_left.mpr (habs ▸ h))
  have hJ' : jacobiSym m' p = -1 := by rw [← jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  obtain ⟨r, hr, hrN, hr8, hrm, -⟩ := exists_prime_modEq (n₁ := 8) (n₂ := m₁) (n₃ := 1)
    (c₁ := 1) (c₂ := p * ((m₁ + 1) / 2)) (c₃ := 0)
    (Nat.coprime_comm.mp ((show (8 : ℕ) = 2 ^ 3 by norm_num) ▸
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hm₁))) (Nat.coprime_one_right _)
    (Nat.coprime_one_right _) (by norm_num) (Nat.Coprime.mul_left hpm₁ (half_coprime hm₁))
    (Nat.coprime_one_right _) (by norm_num) hm₁.pos one_pos (p + m'.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hr4 : r % 4 = 1 := by
    have : r % 8 = 1 := hr8
    omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hpr : p ≠ r := by omega
  have h2rm : 2 * r ≡ p [MOD m₁] := by
    have h2 := hrm.mul_left 2
    have h3 : 2 * (p * ((m₁ + 1) / 2)) = p + m₁ * p := by
      have : 2 * ((m₁ + 1) / 2) = m₁ + 1 := by obtain ⟨k, rfl⟩ := hm₁; omega
      calc 2 * (p * ((m₁ + 1) / 2)) = p * (2 * ((m₁ + 1) / 2)) := by ring
        _ = p + m₁ * p := by rw [this]; ring
    rw [h3] at h2
    exact h2.trans (by rw [Nat.ModEq, Nat.add_mul_mod_self_left])
  have h2rm' : (2 * r : ℤ) ≡ p [ZMOD m'] := by
    have h1 := Int.natCast_modEq_iff.mpr h2rm
    push_cast at h1
    rw [Int.modEq_iff_dvd] at h1 ⊢
    exact Int.natAbs_dvd.mp (habs ▸ h1)
  have hp2r : IsCoprime (p : ℤ) (2 * r) :=
    IsCoprime.mul_right (Int.isCoprime_two_right.mpr (by exact_mod_cast hpodd))
      (Nat.Coprime.isCoprime ((Nat.coprime_primes hpp hr).mpr hpr))
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_two hr hr4
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := m') (B := 1) (T := p * (2 * r)) hm0
    one_pos (by have := hpp.pos; have := hr.pos; positivity) hm' squarefree_one
    (squarefree_prime_mul_two_mul hpp hr hpr hpodd hrodd) isCoprime_one_right isCoprime_one_left
    (IsCoprime.mul_right (isCoprime_of_not_dvd hpp hpm).symm (IsCoprime.mul_right
      (Int.isCoprime_two_right.mpr hm'odd)
      (isCoprime_of_not_dvd hr (not_dvd_of_lt hm0 (by omega))).symm))
    (aniso_one hm' (by omega))
    (exists_sq_modEq_mul hp2r
      (exists_sq_modEq_of_legendreSym_eq_one (by
        rw [mul_one, neg_eq_neg_one_mul, legendreSym.mul,
          legendreSym_neg_one_of_mod_four_eq_three hp, hJ]
        norm_num))
      (exists_sq_modEq_mul (Int.isCoprime_two_left.mpr (by exact_mod_cast hrodd))
        (exists_sq_modEq_two _) (exists_sq_modEq_of_legendreSym_eq_one (by
          have hJm : jacobiSym r m₁ = ZMod.χ₈ (m₁ : ZMod 8) * jacobiSym p m₁ := by
            have h1 := jacobiSym_congr_left h2rm
            rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_ofNat, jacobiSym.at_two hm₁] at h1
            rw [← h1, ← mul_assoc, ← sq]
            have : ZMod.χ₈ (m₁ : ZMod 8) ^ 2 = 1 := by
              rw [ZMod.χ₈_nat_mod_eight]
              rcases (by omega : m₁ % 8 = 1 ∨ m₁ % 8 = 3 ∨ m₁ % 8 = 5 ∨ m₁ % 8 = 7) with
                h' | h' | h' | h' <;> rw [h'] <;> decide
            rw [this, one_mul]
          have hfin : ZMod.χ₈ (m₁ : ZMod 8) * jacobiSym p m₁ = 1 := by
            rw [jacobiSym_recip_three hp hm₁]
            rw [jacobiSym_eq_sign_natAbs (m := m') hp, habs] at hJ'
            rw [ZMod.χ₈_nat_mod_eight]
            rcases Int.natAbs_eq m' with he | he <;> rw [habs] at he
            · rw [ite_eq_right (show ¬m' < 0 by omega), one_mul] at hJ'
              rw [ite_eq_right (show ¬m₁ % 4 = 3 by omega), one_mul, show m₁ % 8 = 5 by omega, hJ']
              decide
            · rw [ite_eq_left (show m' < 0 by omega)] at hJ'
              rw [ite_eq_left (show m₁ % 4 = 3 by omega), show m₁ % 8 = 3 by omega]
              have h1 : jacobiSym m₁ p = 1 := by linear_combination -hJ'
              rw [h1]
              decide
          rw [mul_one, jacobiSym.legendreSym.to_jacobiSym, neg_eq_neg_one_mul, jacobiSym.mul_left,
            jacobiSym.at_neg_one hrodd, ZMod.χ₄_nat_mod_four, hr4, jacobiSym_eq_natAbs hr4, habs,
            jacobiSym.quadratic_reciprocity_one_mod_four' hm₁ hr4, hJm, hfin]
          decide))))
    ⟨0, Int.modEq_one⟩
    ⟨p, by
      calc (p : ℤ) ^ 2 = p * p := sq _
        _ ≡ p * (2 * r) [ZMOD m'] := h2rm'.symm.mul_left _
        _ = 1 * (p * (2 * r)) := by ring⟩
  have hu : u ≠ 0 := by
    rintro rfl
    refine hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := 1) (c' := 2 * r) (u := v) (v := w)
      (not_dvd_unit (Or.inl rfl)) ?_ (by linear_combination huvw)).2
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
    · have := Int.le_of_dvd (by norm_num) h; omega
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hpp hr).mp (Int.natCast_dvd_natCast.mp h))
  exact exists_of_combine (κ := p) (A := m') (B := 1) (T := 2 * r) (u := u) (v := v) (w := w)
    hz hu hxyz (by linear_combination huvw)

/-- The "if" half of Robinson's Lemma 1. -/
private theorem lemma_one_if {p : ℕ} [hpf : Fact p.Prime] (hp : p % 4 = 3) {M : ℚ} (hM : M ≠ 0)
    (h1 : ¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = 1)
    (h2 : ¬∃ (k : ℤ) (S : ℚ), M = k * S ^ 2 ∧ k ≡ p [ZMOD 8]) :
    ∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - p * Z ^ 2 = M := by
  have hpp := hpf.out
  obtain ⟨m₀, S, hsq, hS, rfl⟩ := exists_squarefree_mul_sq hM
  suffices H : ∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - p * Z ^ 2 = m₀ by
    obtain ⟨X, Y, Z, h⟩ := H
    exact ⟨S * X, S * Y, S * Z, by linear_combination S ^ 2 * h⟩
  have h2' : ¬m₀ ≡ p [ZMOD 8] := fun h => h2 ⟨m₀, S, rfl, h⟩
  by_cases hpm : (p : ℤ) ∣ m₀
  · obtain ⟨m', rfl⟩ := hpm
    have hm' : Squarefree m' := hsq.of_mul_right
    have hpm' : ¬(p : ℤ) ∣ m' := by
      rintro ⟨d, rfl⟩
      have := hsq (p : ℤ) ⟨d, by ring⟩
      exact (Nat.prime_iff_prime_int.mp hpp).not_isUnit this
    have hJ : legendreSym p m' = -1 := by
      rcases legendreSym.eq_one_or_neg_one p (a := m') (by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpm') with h | h
      · exact absurd ⟨m', S, by push_cast; ring, h⟩ h1
      · exact h
    suffices H : ∃ X Y Z : ℚ, (m' : ℚ) = p * (X ^ 2 + 1 * Y ^ 2) - 1 * Z ^ 2 by
      obtain ⟨X, Y, Z, h⟩ := H
      exact ⟨p * X, p * Y, Z, by push_cast; linear_combination (-(p : ℚ)) * h⟩
    by_cases hm1 : m' = -1
    · exact ⟨0, 0, 1, by rw [hm1]; push_cast; ring⟩
    obtain ⟨e, m₁, he1, hm₁, habs⟩ := exists_two_pow_mul_odd hm'
    by_cases h4 : e = 1 ∨ m' % 4 = 3
    · exact lemma_one_if_B1 hp hm' hpm' hJ hm1 he1 hm₁ habs h4
    · have he : e = 0 := by omega
      subst he
      rw [pow_zero, one_mul] at habs
      have hodd : m' % 2 = 1 := by
        rcases Int.natAbs_eq m' with h | h <;> rw [habs] at h <;>
          · have := Nat.odd_iff.mp hm₁; omega
      have h8 : m' % 8 = 5 := by
        by_contra h8
        have : m' % 8 = 1 := by omega
        refine h2' (Int.modEq_iff_dvd.mpr ?_)
        obtain ⟨t, ht⟩ : (8 : ℤ) ∣ m' - 1 := by omega
        exact ⟨-(p * t), by linear_combination (-(p : ℤ)) * ht⟩
      exact lemma_one_if_B2 hp hm' hpm' hJ hm₁ habs h8
  · obtain ⟨e, m₁, he1, hm₁, habs⟩ := exists_two_pow_mul_odd hsq
    suffices H : ∃ X Y Z : ℚ, (m₀ : ℚ) = 1 * (X ^ 2 + 1 * Y ^ 2) - p * Z ^ 2 by
      obtain ⟨X, Y, Z, h⟩ := H
      exact ⟨X, Y, Z, by linear_combination -h⟩
    by_cases h4 : e = 1 ∨ m₀ % 4 = 1
    · exact lemma_one_if_A1 hp hsq hpm he1 hm₁ habs h4
    · have he : e = 0 := by omega
      subst he
      rw [pow_zero, one_mul] at habs
      have hodd : m₀ % 2 = 1 := by
        rcases Int.natAbs_eq m₀ with h | h <;> rw [habs] at h <;>
          · have := Nat.odd_iff.mp hm₁; omega
      exact lemma_one_if_A2 hp hsq hpm hm₁ habs (by omega) h2'

/-- **Robinson's Lemma 1.** Let `p` be a prime with `p ≡ 3 (mod 4)` and let `M` be a nonzero
rational number. Then `X ^ 2 + Y ^ 2 - p Z ^ 2 = M` has a solution in rational numbers `X, Y, Z`
if and only if `M` is of neither of the forms `p k S ^ 2` with `(k / p) = 1` and `k S ^ 2` with
`k ≡ p (mod 8)`, where `k` is an integer and `S` a rational number.

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 1, p. 107: "If `p` is a prime `≡ 3 (mod 4)` then `X² + Y² − pZ²` represents a nonzero
rational number `M`, if and only if `M` is not of the form `pk·S²` with `(k/p) = 1` or `k·S²` with
`k ≡ p (mod 8)`." Capital letters denote rationals and small letters integers (p. 106). Robinson
states it without proof, as a special case of a theorem of Hasse (p. 107). The "only if" half is
`lemma_one_only_if`. For the "if" half, write `M = m₀ S ^ 2` with `m₀` a squarefree integer; an
auxiliary prime `r ≡ 1 (mod 4)` from Dirichlet's theorem, with `T = r`, `2 r`, `p r` or `2 p r`
according to `p ∣ m₀` and the class of `m₀` modulo `8`, is represented both by `X ^ 2 + Y ^ 2` and,
by Legendre's theorem, by a binary form attached to `m₀`. -/
theorem lemma_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {M : ℚ} (hM : M ≠ 0) :
    (∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - p * Z ^ 2 = M) ↔
      (¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = 1) ∧
        ¬∃ (k : ℤ) (S : ℚ), M = k * S ^ 2 ∧ k ≡ p [ZMOD 8] :=
  ⟨lemma_one_only_if hp hM, fun h => lemma_one_if hp hM h.1 h.2⟩

/-! ### Robinson's Lemma 2: sufficiency of the conditions -/

/-- `exists_prime_modEq` with the residue classes given by integers. -/
private theorem exists_prime_intModEq {n₁ n₂ n₃ : ℕ} {c₁ c₂ c₃ : ℤ} (h12 : n₁.Coprime n₂)
    (h13 : n₁.Coprime n₃) (h23 : n₂.Coprime n₃) (hc₁ : IsCoprime c₁ n₁) (hc₂ : IsCoprime c₂ n₂)
    (hc₃ : IsCoprime c₃ n₃) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (N : ℕ) :
    ∃ r : ℕ, r.Prime ∧ N < r ∧ (r : ℤ) ≡ c₁ [ZMOD n₁] ∧ (r : ℤ) ≡ c₂ [ZMOD n₂] ∧
      (r : ℤ) ≡ c₃ [ZMOD n₃] := by
  have key : ∀ {c : ℤ} {n : ℕ}, 0 < n → IsCoprime c n →
      ((c % n).toNat : ℤ) = c % n ∧ (c % n).toNat.Coprime n := by
    intro c n hn hc
    have h0 : 0 ≤ c % n := Int.emod_nonneg c (by exact_mod_cast hn.ne')
    have he : ((c % n).toNat : ℤ) = c % n := Int.toNat_of_nonneg h0
    refine ⟨he, Nat.isCoprime_iff_coprime.mp ?_⟩
    rw [he, Int.emod_def]
    obtain ⟨u, v, huv⟩ := hc
    exact ⟨u, v + u * (c / n), by linear_combination huv⟩
  have conv : ∀ {r : ℕ} {c : ℤ} {n : ℕ}, ((c % n).toNat : ℤ) = c % n →
      r ≡ (c % n).toNat [MOD n] → (r : ℤ) ≡ c [ZMOD n] := by
    intro r c n he h
    refine (Int.natCast_modEq_iff.mpr h).trans ?_
    rw [he]
    exact Int.mod_modEq c n
  obtain ⟨e₁, h₁⟩ := key hn₁ hc₁
  obtain ⟨e₂, h₂⟩ := key hn₂ hc₂
  obtain ⟨e₃, h₃⟩ := key hn₃ hc₃
  obtain ⟨r, hr, hrN, hr₁, hr₂, hr₃⟩ := exists_prime_modEq h12 h13 h23 h₁ h₂ h₃ hn₁ hn₂ hn₃ N
  exact ⟨r, hr, hrN, conv e₁ hr₁, conv e₂ hr₂, conv e₃ hr₃⟩

/-- The Jacobi symbol `(a / b)` depends only on the class of the odd number `b` modulo
`4 |a|`. -/
private theorem jacobiSym_congr_right {a : ℤ} {b c : ℕ} (hb : Odd b) (hc : Odd c)
    (h : (b : ℤ) ≡ c [ZMOD (4 * a.natAbs : ℕ)]) : jacobiSym a b = jacobiSym a c := by
  have h' : b % (4 * a.natAbs) = c % (4 * a.natAbs) := Int.natCast_modEq_iff.mp h
  rw [jacobiSym.mod_right a hb, jacobiSym.mod_right a hc, h']

/-- The Legendre symbol `(a / ℓ)` depends only on the class of `a` modulo `ℓ`. -/
private theorem legendreSym_congr {ℓ : ℕ} [Fact ℓ.Prime] {a b : ℤ} (h : a ≡ b [ZMOD ℓ]) :
    legendreSym ℓ a = legendreSym ℓ b := by
  rw [legendreSym.mod, h.eq, ← legendreSym.mod]

/-- A prime does not divide a different prime. -/
private theorem not_dvd_of_prime_ne {ℓ r : ℕ} (hℓ : ℓ.Prime) (hr : r.Prime) (h : ℓ ≠ r) :
    ¬(ℓ : ℤ) ∣ r := by
  rw [Int.natCast_dvd_natCast]
  exact fun hd => h ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp hd)

/-- `4 a` is prime to an odd prime `ℓ` not dividing `a`. -/
private theorem coprime_four_mul {a ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (h : ¬ℓ ∣ a) :
    (4 * a).Coprime ℓ := by
  refine Nat.Coprime.mul_left ?_ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr h).symm
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hℓ).mpr (Ne.symm hℓ2))

/-- In a squarefree integer `ℓ k`, the prime `ℓ` does not divide `k`. -/
private theorem not_dvd_of_squarefree_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {k : ℤ}
    (h : Squarefree ((ℓ : ℤ) * k)) : ¬(ℓ : ℤ) ∣ k := by
  rintro ⟨c, rfl⟩
  exact (Nat.prime_iff_prime_int.mp hℓ).not_isUnit (h ℓ ⟨c, by ring⟩)

/-- A Legendre symbol of an integer prime to `ℓ` that is not `-1` is `1`. -/
private theorem legendreSym_eq_one_of_ne {ℓ : ℕ} [Fact ℓ.Prime] {k : ℤ} (hk : ¬(ℓ : ℤ) ∣ k)
    (h : legendreSym ℓ k ≠ -1) : legendreSym ℓ k = 1 :=
  (legendreSym.eq_one_or_neg_one ℓ (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])).resolve_right h

/-- The square of the Legendre symbol of an integer prime to `ℓ` is `1`. -/
private theorem legendreSym_mul_self {ℓ : ℕ} [Fact ℓ.Prime] {k : ℤ} (hk : ¬(ℓ : ℤ) ∣ k) :
    legendreSym ℓ k * legendreSym ℓ k = 1 := by
  rcases legendreSym.eq_one_or_neg_one ℓ (a := k)
    (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) with h | h <;> rw [h] <;> norm_num

/-- `(-q / r) = 1` for odd primes `q` and `r` with `r ≡ 1 (mod q)`, and `r ≡ 1` or
`r ≡ q (mod 4)`. -/
private theorem legendreSym_neg_eq_one {q r : ℕ} [hq : Fact q.Prime] [hr : Fact r.Prime]
    (hq2 : q ≠ 2) (hr2 : r ≠ 2) (hrq : (r : ℤ) ≡ 1 [ZMOD q]) (hr4 : r % 4 = 1 ∨ r % 4 = q % 4) :
    legendreSym r (-q) = 1 := by
  have hqo : Odd q := hq.out.odd_of_ne_two hq2
  have hro : Odd r := hr.out.odd_of_ne_two hr2
  have hJ : jacobiSym r q = 1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym_congr hrq, legendreSym.at_one]
  rw [neg_eq_neg_one_mul, legendreSym.mul, jacobiSym.legendreSym.to_jacobiSym r q]
  by_cases h1 : r % 4 = 1
  · rw [legendreSym_neg_one_of_mod_four_eq_one h1,
      jacobiSym.quadratic_reciprocity_one_mod_four' hqo h1, hJ, one_mul]
  · have h3 : r % 4 = 3 := by have := Nat.odd_iff.mp hro; omega
    have h3' : q % 4 = 3 := by omega
    rw [legendreSym_neg_one_of_mod_four_eq_three h3,
      jacobiSym.quadratic_reciprocity_three_mod_four h3' h3, hJ]
    norm_num

/-- A prime `r ≠ q` with `r ≡ 1 (mod q)` and `(-q / r) = 1` is represented by
`x ^ 2 + q y ^ 2` (Legendre's theorem). -/
private theorem exists_norm_eq {q r : ℕ} [hq : Fact q.Prime] [hr : Fact r.Prime] (hqr : q ≠ r)
    (hrq : (r : ℤ) ≡ 1 [ZMOD q]) (hneg : legendreSym r (-q) = 1) :
    ∃ x y z : ℤ, z ≠ 0 ∧ x ^ 2 + q * y ^ 2 = r * z ^ 2 := by
  obtain ⟨x, y, z, hz, h⟩ := exists_of_legendre (A := 1) (B := q) (r := r) one_pos hq.out.pos
    hr.out squarefree_one hq.out.prime.squarefree (Nat.coprime_one_left q)
    (Nat.coprime_one_left r) ((Nat.coprime_primes hq.out hr.out).mpr hqr)
    (exists_sq_modEq_of_legendreSym_eq_one (by simpa using hneg))
    ⟨1, by simpa using hrq.symm⟩ ⟨0, Int.modEq_one⟩
  exact ⟨x, y, z, hz, by simpa using h⟩

/-- Case `p ∤ m`, `q ∤ m` of the "if" half of Lemma 2, for a squarefree integer `m`: a prime
`r ≡ p (mod 4 |m|)`, `r ≡ m (mod p)`, `r ≡ 1 (mod q)` is represented by `X ^ 2 + q Y ^ 2` and
by `m U ^ 2 + p V ^ 2`. -/
private theorem lemma_two_if_coprime {p q : ℕ} [hpf : Fact p.Prime] [hqf : Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) (hpq : p ≠ q) {m : ℤ} (hm : Squarefree m)
    (hpm : ¬(p : ℤ) ∣ m) (hqm : ¬(q : ℤ) ∣ m) :
    ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = m := by
  have hpp := hpf.out
  have hqq := hqf.out
  have hm0 : m ≠ 0 := hm.ne_zero
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have h4p := coprime_four_mul hpp hp2 (fun h => hpm (Int.natCast_dvd.mpr h))
  have h4q := coprime_four_mul hqq hq (fun h => hqm (Int.natCast_dvd.mpr h))
  obtain ⟨r, hr, hrN, hr₁, hr₂, hr₃⟩ := exists_prime_intModEq (n₁ := 4 * m.natAbs) (n₂ := p)
    (n₃ := q) (c₁ := p) (c₂ := m) (c₃ := 1) h4p h4q ((Nat.coprime_primes hpp hqq).mpr hpq)
    (Nat.isCoprime_iff_coprime.mpr h4p.symm) ((isCoprime_of_not_dvd hpp hpm).symm)
    isCoprime_one_left
    (by have := Int.natAbs_pos.mpr hm0; omega) hpp.pos hqq.pos (p + q + m.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hp2' := hpp.two_le
  have hrp : p ≠ r := by omega
  have hrq : q ≠ r := by omega
  have hr2 : r ≠ 2 := by omega
  have hro : Odd r := hr.odd_of_ne_two hr2
  have hr4 : r % 4 = 1 := by
    have h := (hr₁.of_dvd (by push_cast; exact dvd_mul_right 4 _) : (r : ℤ) ≡ p [ZMOD 4]).eq
    omega
  have hrm : (r : ℤ) ≡ p [ZMOD m] :=
    hr₁.of_dvd (by push_cast; exact Dvd.dvd.mul_left ((dvd_abs m m).mpr dvd_rfl) 4)
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_eq hrq hr₃
    (legendreSym_neg_eq_one hq hr2 hr₃ (Or.inl hr4))
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := m) (B := p) (T := r) hm0
    (by exact_mod_cast hpp.pos) (by exact_mod_cast hr.pos) hm
    (Int.squarefree_natCast.mpr hpp.squarefree) (Int.squarefree_natCast.mpr hr.squarefree)
    ((isCoprime_of_not_dvd hpp hpm).symm)
    (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpp hr).mpr hrp))
    ((isCoprime_of_not_dvd hr (not_dvd_of_lt hm0 (by omega))).symm)
    (fun x y h => eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := -m) (c' := 1) (by rwa [dvd_neg])
      (not_dvd_unit (Or.inl rfl)) (by linear_combination -h))
    (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [show -(m * (p : ℤ)) = -1 * m * p by ring, legendreSym.mul, legendreSym.mul,
        legendreSym_neg_one_of_mod_four_eq_one hr4, jacobiSym.legendreSym.to_jacobiSym r m,
        jacobiSym_congr_right hro hpo hr₁, ← jacobiSym.legendreSym.to_jacobiSym p m,
        jacobiSym.legendreSym.to_jacobiSym r p, jacobiSym.quadratic_reciprocity_one_mod_four hp hro,
        ← jacobiSym.legendreSym.to_jacobiSym p r, legendreSym_congr hr₂, one_mul]
      exact legendreSym_mul_self hpm))
    ⟨m, by rw [sq]; exact (hr₂.mul_left m).symm⟩
    ⟨p, by rw [sq]; exact (hrm.mul_left p).symm⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := r) (c' := 1)
      (not_dvd_of_prime_ne hpp hr hrp) (not_dvd_unit (Or.inl rfl)) (u := w) (v := v)
      (by linear_combination -huvw)).1
  obtain ⟨X, Y, Z, h⟩ := exists_of_combine (a := q) (κ := 1) (A := m) (B := p) (T := r) (v := v)
    (w := w) hz hu hxyz (by linear_combination huvw)
  refine ⟨X, Y, Z, ?_⟩
  push_cast at h
  linear_combination -h

/-- Case `m = p k` with `p ∤ k`, `q ∤ k` and `(k / p) = 1` of the "if" half of Lemma 2: for
`k ≠ -1`, a prime `r ≡ p (mod 4 |k|)`, `r ≡ 1 (mod q)` is represented by `X ^ 2 + q Y ^ 2`, and
`p r` by `k U ^ 2 + V ^ 2`. -/
private theorem lemma_two_if_dvd_left {p q : ℕ} [hpf : Fact p.Prime] [hqf : Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) {k : ℤ} (hk : Squarefree k)
    (hpk : ¬(p : ℤ) ∣ k) (hqk : ¬(q : ℤ) ∣ k) (hkp : legendreSym p k = 1) :
    ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = p * k := by
  by_cases hk1 : k = -1
  · subst hk1
    exact ⟨0, 0, 1, by push_cast; ring⟩
  have hpp := hpf.out
  have hqq := hqf.out
  have hk0 : k ≠ 0 := hk.ne_zero
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have h4p := coprime_four_mul hpp hp2 (fun h => hpk (Int.natCast_dvd.mpr h))
  have h4q := coprime_four_mul hqq hq (fun h => hqk (Int.natCast_dvd.mpr h))
  obtain ⟨r, hr, hrN, hr₁, hr₃, -⟩ := exists_prime_intModEq (n₁ := 4 * k.natAbs) (n₂ := q)
    (n₃ := 1) (c₁ := p) (c₂ := 1) (c₃ := 1) h4q (Nat.coprime_one_right _)
    (Nat.coprime_one_right _) (Nat.isCoprime_iff_coprime.mpr h4p.symm) isCoprime_one_left
    isCoprime_one_left (by have := Int.natAbs_pos.mpr hk0; omega) hqq.pos one_pos
    (p + q + k.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hp2' := hpp.two_le
  have hrp : p ≠ r := by omega
  have hrq : q ≠ r := by omega
  have hr2 : r ≠ 2 := by omega
  have hro : Odd r := hr.odd_of_ne_two hr2
  have hr4 : r % 4 = 1 := by
    have h := (hr₁.of_dvd (by push_cast; exact dvd_mul_right 4 _) : (r : ℤ) ≡ p [ZMOD 4]).eq
    omega
  have hrk : (r : ℤ) ≡ p [ZMOD k] :=
    hr₁.of_dvd (by push_cast; exact Dvd.dvd.mul_left ((dvd_abs k k).mpr dvd_rfl) 4)
  have hnegp : legendreSym p (-k) = 1 := by
    rw [neg_eq_neg_one_mul, legendreSym.mul, legendreSym_neg_one_of_mod_four_eq_one hp, hkp,
      mul_one]
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_eq hrq hr₃
    (legendreSym_neg_eq_one hq hr2 hr₃ (Or.inl hr4))
  have hpr : IsCoprime (p : ℤ) r :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpp hr).mpr hrp)
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := k) (B := 1) (T := p * r) hk0 one_pos
    (by have := hpp.pos; have := hr.pos; positivity) hk squarefree_one
    (by
      have := Int.squarefree_natCast.mpr (Nat.squarefree_mul_iff.mpr
        ⟨(Nat.coprime_primes hpp hr).mpr hrp, hpp.squarefree, hr.squarefree⟩)
      push_cast at this
      exact this)
    isCoprime_one_right isCoprime_one_left
    (((isCoprime_of_not_dvd hpp hpk).symm).mul_right
      ((isCoprime_of_not_dvd hr (not_dvd_of_lt hk0 (by omega))).symm))
    (aniso_one hk hk1)
    (by
      refine exists_sq_modEq_mul hpr (exists_sq_modEq_of_legendreSym_eq_one ?_)
        (exists_sq_modEq_of_legendreSym_eq_one ?_)
      · rw [mul_one]; exact hnegp
      · rw [mul_one, jacobiSym.legendreSym.to_jacobiSym,
          jacobiSym_congr_right hro hpo (by rw [Int.natAbs_neg]; exact hr₁),
          ← jacobiSym.legendreSym.to_jacobiSym]
        exact hnegp)
    ⟨0, Int.modEq_one⟩
    ⟨p, by rw [one_mul, sq]; exact (hrk.mul_left p).symm⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := 1) (c' := r) (not_dvd_unit (Or.inl rfl))
      (not_dvd_of_prime_ne hpp hr hrp) (u := v) (v := w)
      (by linear_combination huvw)).2
  obtain ⟨X, Y, Z, h⟩ := exists_of_combine (a := q) (κ := p) (A := k) (B := 1) (T := r) (v := v)
    (w := w) hz hu hxyz (by linear_combination huvw)
  refine ⟨p * X, p * Y, Z, ?_⟩
  push_cast at h
  linear_combination (-(p : ℚ)) * h

/-- Case `m = q k` with `p ∤ k`, `q ∤ k` and `(k / q) = 1` of the "if" half of Lemma 2: a prime
`r ≡ p q (mod 4 |k|)`, `r ≡ k (mod p)`, `r ≡ 1 (mod q)` is represented by `X ^ 2 + q Y ^ 2` and
by `k U ^ 2 + p q V ^ 2`. -/
private theorem lemma_two_if_dvd_right {p q : ℕ} [hpf : Fact p.Prime] [hqf : Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) (hpq : p ≠ q) {k : ℤ} (hk : Squarefree k)
    (hpk : ¬(p : ℤ) ∣ k) (hqk : ¬(q : ℤ) ∣ k) (hkq : legendreSym q k = 1) :
    ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = q * k := by
  have hpp := hpf.out
  have hqq := hqf.out
  have hk0 : k ≠ 0 := hk.ne_zero
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have hqo : Odd q := hqq.odd_of_ne_two hq
  have : NeZero p := ⟨hpp.ne_zero⟩
  have : NeZero q := ⟨hqq.ne_zero⟩
  have h4p := coprime_four_mul hpp hp2 (fun h => hpk (Int.natCast_dvd.mpr h))
  have h4q := coprime_four_mul hqq hq (fun h => hqk (Int.natCast_dvd.mpr h))
  obtain ⟨r, hr, hrN, hr₁, hr₂, hr₃⟩ := exists_prime_intModEq (n₁ := 4 * k.natAbs) (n₂ := p)
    (n₃ := q) (c₁ := p * q) (c₂ := k) (c₃ := 1) h4p h4q ((Nat.coprime_primes hpp hqq).mpr hpq)
    ((Nat.isCoprime_iff_coprime.mpr h4p.symm).mul_left (Nat.isCoprime_iff_coprime.mpr h4q.symm))
    ((isCoprime_of_not_dvd hpp hpk).symm) isCoprime_one_left
    (by have := Int.natAbs_pos.mpr hk0; omega) hpp.pos hqq.pos (p + q + k.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hp2' := hpp.two_le
  have hrp : p ≠ r := by omega
  have hrq : q ≠ r := by omega
  have hr2 : r ≠ 2 := by omega
  have hro : Odd r := hr.odd_of_ne_two hr2
  have hr4 : r % 4 = q % 4 := by
    have h := (hr₁.of_dvd (by push_cast; exact dvd_mul_right 4 _) : (r : ℤ) ≡ p * q [ZMOD 4])
    have hp4 : (p : ℤ) ≡ 1 [ZMOD 4] := by
      unfold Int.ModEq
      omega
    have h' := (h.trans (hp4.mul_right q)).eq
    rw [one_mul] at h'
    omega
  have hrk : (r : ℤ) ≡ p * q [ZMOD k] :=
    hr₁.of_dvd (by push_cast; exact Dvd.dvd.mul_left ((dvd_abs k k).mpr dvd_rfl) 4)
  have hneg := legendreSym_neg_eq_one hq hr2 hr₃ (Or.inr hr4)
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_eq hrq hr₃ hneg
  have hcop : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → IsCoprime (a : ℤ) b := fun ha hb hab =>
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes ha hb).mpr hab)
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := k) (B := p * q) (T := r) hk0
    (by have := hpp.pos; have := hqq.pos; positivity) (by exact_mod_cast hr.pos) hk
    (by
      have := Int.squarefree_natCast.mpr (Nat.squarefree_mul_iff.mpr
        ⟨(Nat.coprime_primes hpp hqq).mpr hpq, hpp.squarefree, hqq.squarefree⟩)
      push_cast at this
      exact this)
    (Int.squarefree_natCast.mpr hr.squarefree)
    (((isCoprime_of_not_dvd hpp hpk).symm).mul_right ((isCoprime_of_not_dvd hqq hqk).symm))
    ((hcop hpp hr hrp).mul_left (hcop hqq hr hrq))
    ((isCoprime_of_not_dvd hr (not_dvd_of_lt hk0 (by omega))).symm)
    (fun x y h => eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := -k) (c' := q) (by rwa [dvd_neg])
      (not_dvd_of_prime_ne hpp hqq hpq) (by linear_combination -h))
    (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [show -(k * ((p : ℤ) * q)) = -(q : ℤ) * k * p by ring, legendreSym.mul, legendreSym.mul,
        hneg, jacobiSym.legendreSym.to_jacobiSym r k,
        jacobiSym_congr_right (c := p * q) hro (hpo.mul hqo) (by push_cast at hr₁ ⊢; exact hr₁),
        jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym p k,
        ← jacobiSym.legendreSym.to_jacobiSym q k, hkq, jacobiSym.legendreSym.to_jacobiSym r p,
        jacobiSym.quadratic_reciprocity_one_mod_four hp hro,
        ← jacobiSym.legendreSym.to_jacobiSym p r, legendreSym_congr hr₂, one_mul, mul_one]
      exact legendreSym_mul_self hpk))
    (exists_sq_modEq_mul (hcop hpp hqq hpq) ⟨k, by rw [sq]; exact (hr₂.mul_left k).symm⟩
      (exists_sq_modEq_of_legendreSym_eq_one (by
        rw [legendreSym.mul, hkq, legendreSym_congr hr₃, legendreSym.at_one, mul_one])))
    ⟨p * q, by rw [sq]; exact (hrk.mul_left _).symm⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := r) (c' := q)
      (not_dvd_of_prime_ne hpp hr hrp) (not_dvd_of_prime_ne hpp hqq hpq) (u := w) (v := v)
      (by linear_combination -huvw)).1
  obtain ⟨X, Y, Z, h⟩ := exists_of_combine (a := q) (κ := 1) (A := k) (B := p * q) (T := r)
    (v := v) (w := w) hz hu hxyz (by linear_combination huvw)
  refine ⟨q * Y, X, q * Z, ?_⟩
  push_cast at h
  linear_combination (-(q : ℚ)) * h

/-- Case `m = p q k` with `p ∤ k`, `q ∤ k`, `(k / p) = -1` and `(k / q) = -1` of the "if" half
of Lemma 2: a prime `r ≡ p q (mod 4 |k|)`, `r ≡ 1 (mod q)` is represented by `X ^ 2 + q Y ^ 2`,
and `p r` by `k U ^ 2 + q V ^ 2`. -/
private theorem lemma_two_if_dvd_both {p q : ℕ} [hpf : Fact p.Prime] [hqf : Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) (hqp : legendreSym p q = -1) (hpq : p ≠ q) {k : ℤ}
    (hk : Squarefree k) (hpk : ¬(p : ℤ) ∣ k) (hqk : ¬(q : ℤ) ∣ k) (hkp : legendreSym p k = -1)
    (hkq : legendreSym q k = -1) :
    ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = p * q * k := by
  have hpp := hpf.out
  have hqq := hqf.out
  have hk0 : k ≠ 0 := hk.ne_zero
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have hqo : Odd q := hqq.odd_of_ne_two hq
  have : NeZero p := ⟨hpp.ne_zero⟩
  have : NeZero q := ⟨hqq.ne_zero⟩
  have h4p := coprime_four_mul hpp hp2 (fun h => hpk (Int.natCast_dvd.mpr h))
  have h4q := coprime_four_mul hqq hq (fun h => hqk (Int.natCast_dvd.mpr h))
  obtain ⟨r, hr, hrN, hr₁, hr₃, -⟩ := exists_prime_intModEq (n₁ := 4 * k.natAbs) (n₂ := q)
    (n₃ := 1) (c₁ := p * q) (c₂ := 1) (c₃ := 1) h4q (Nat.coprime_one_right _)
    (Nat.coprime_one_right _)
    ((Nat.isCoprime_iff_coprime.mpr h4p.symm).mul_left (Nat.isCoprime_iff_coprime.mpr h4q.symm))
    isCoprime_one_left isCoprime_one_left (by have := Int.natAbs_pos.mpr hk0; omega) hqq.pos
    one_pos (p + q + k.natAbs)
  have : Fact r.Prime := ⟨hr⟩
  have hp2' := hpp.two_le
  have hrp : p ≠ r := by omega
  have hrq : q ≠ r := by omega
  have hr2 : r ≠ 2 := by omega
  have hro : Odd r := hr.odd_of_ne_two hr2
  have hr4 : r % 4 = q % 4 := by
    have h := (hr₁.of_dvd (by push_cast; exact dvd_mul_right 4 _) : (r : ℤ) ≡ p * q [ZMOD 4])
    have hp4 : (p : ℤ) ≡ 1 [ZMOD 4] := by
      unfold Int.ModEq
      omega
    have h' := (h.trans (hp4.mul_right q)).eq
    rw [one_mul] at h'
    omega
  have hrk : (r : ℤ) ≡ p * q [ZMOD k] :=
    hr₁.of_dvd (by push_cast; exact Dvd.dvd.mul_left ((dvd_abs k k).mpr dvd_rfl) 4)
  have hneg := legendreSym_neg_eq_one hq hr2 hr₃ (Or.inr hr4)
  obtain ⟨x, y, z, hz, hxyz⟩ := exists_norm_eq hrq hr₃ hneg
  have hcop : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → IsCoprime (a : ℤ) b := fun ha hb hab =>
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes ha hb).mpr hab)
  have hpq' : legendreSym q p = -1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp hq, hqp]
  obtain ⟨u, v, w, hw, huvw⟩ := exists_of_legendre' (A := k) (B := q) (T := p * r) hk0
    (by exact_mod_cast hqq.pos) (by have := hpp.pos; have := hr.pos; positivity) hk
    (Int.squarefree_natCast.mpr hqq.squarefree)
    (by
      have := Int.squarefree_natCast.mpr (Nat.squarefree_mul_iff.mpr
        ⟨(Nat.coprime_primes hpp hr).mpr hrp, hpp.squarefree, hr.squarefree⟩)
      push_cast at this
      exact this)
    ((isCoprime_of_not_dvd hqq hqk).symm) ((hcop hqq hpp hpq.symm).mul_right (hcop hqq hr hrq))
    (((isCoprime_of_not_dvd hpp hpk).symm).mul_right
      ((isCoprime_of_not_dvd hr (not_dvd_of_lt hk0 (by omega))).symm))
    (fun x y h => eq_zero_of_mul_sq_eq_mul_sq (ℓ := q) (c := -k) (c' := 1) (by rwa [dvd_neg])
      (not_dvd_unit (Or.inl rfl)) (by linear_combination -h))
    (by
      refine exists_sq_modEq_mul (hcop hpp hr hrp) (exists_sq_modEq_of_legendreSym_eq_one ?_)
        (exists_sq_modEq_of_legendreSym_eq_one ?_)
      · rw [show -(k * (q : ℤ)) = -1 * k * q by ring, legendreSym.mul, legendreSym.mul,
          legendreSym_neg_one_of_mod_four_eq_one hp, hkp, hqp]
        norm_num
      · rw [show -(k * (q : ℤ)) = -(q : ℤ) * k by ring, legendreSym.mul, hneg,
          jacobiSym.legendreSym.to_jacobiSym r k,
          jacobiSym_congr_right (c := p * q) hro (hpo.mul hqo) (by push_cast at hr₁ ⊢; exact hr₁),
          jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym p k,
          ← jacobiSym.legendreSym.to_jacobiSym q k, hkp, hkq]
        norm_num)
    (exists_sq_modEq_of_legendreSym_eq_one (by
      rw [legendreSym.mul, legendreSym.mul, hkq, hpq', legendreSym_congr hr₃, legendreSym.at_one]
      norm_num))
    ⟨p * q, by
      calc ((p : ℤ) * q) ^ 2 = q * p * (p * q) := by ring
        _ ≡ q * p * r [ZMOD k] := (hrk.mul_left _).symm
        _ = q * (p * r) := by ring⟩
  have hu : u ≠ 0 := by
    rintro rfl
    exact hw (eq_zero_of_mul_sq_eq_mul_sq (ℓ := p) (c := q) (c' := r)
      (not_dvd_of_prime_ne hpp hqq hpq) (not_dvd_of_prime_ne hpp hr hrp) (u := v) (v := w)
      (by linear_combination huvw)).2
  obtain ⟨X, Y, Z, h⟩ := exists_of_combine (a := q) (κ := p) (A := k) (B := q) (T := r)
    (v := v) (w := w) hz hu hxyz (by linear_combination huvw)
  refine ⟨p * q * Y, p * X, q * Z, ?_⟩
  push_cast at h
  linear_combination (-(p : ℚ) * q) * h

/-- **Robinson's Lemma 2, sufficiency of the conditions.** Let `p` and `q` be odd primes with
`p ≡ 1 (mod 4)` and `(q / p) = -1`, and let `M` be a nonzero rational number of neither of the
forms `p k S ^ 2` with `(k / p) = -1` and `q k S ^ 2` with `(k / q) = -1`. Then
`X ^ 2 + q Y ^ 2 - p Z ^ 2 = M` has a solution in rational numbers `X, Y, Z`.

Write `M = m S ^ 2` with `m` a squarefree integer. According as `p` and `q` divide `m`, an
auxiliary prime `r` from Dirichlet's theorem is represented both by `X ^ 2 + q Y ^ 2` and, up to
the factor `p` in the cases `p ∣ m`, by a binary form attached to `m`, by Legendre's theorem. -/
private theorem lemma_two_if {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1) (hq : q ≠ 2)
    (hqp : legendreSym p q = -1) {M : ℚ} (hM : M ≠ 0)
    (h1 : ¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = -1)
    (h2 : ¬∃ (k : ℤ) (S : ℚ), M = q * k * S ^ 2 ∧ legendreSym q k = -1) :
    ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = M := by
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  have hpq : p ≠ q := by
    rintro rfl
    rw [(legendreSym.eq_zero_iff p p).mpr (by simp)] at hqp
    norm_num at hqp
  obtain ⟨m, S, hm, hS, rfl⟩ := exists_squarefree_mul_sq hM
  suffices H : ∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = m by
    obtain ⟨X, Y, Z, h⟩ := H
    exact ⟨S * X, S * Y, S * Z, by linear_combination S ^ 2 * h⟩
  have h1' : ∀ k : ℤ, m = p * k → legendreSym p k ≠ -1 := fun k hk hl =>
    h1 ⟨k, S, by rw [hk]; push_cast; ring, hl⟩
  have h2' : ∀ k : ℤ, m = q * k → legendreSym q k ≠ -1 := fun k hk hl =>
    h2 ⟨k, S, by rw [hk]; push_cast; ring, hl⟩
  have hqp' : ¬(q : ℤ) ∣ p := not_dvd_of_prime_ne hqq hpp hpq.symm
  by_cases hpm : (p : ℤ) ∣ m <;> by_cases hqm : (q : ℤ) ∣ m
  · obtain ⟨k₁, rfl⟩ := hpm
    obtain ⟨k, rfl⟩ := ((Nat.prime_iff_prime_int.mp hqq).dvd_or_dvd hqm).resolve_left hqp'
    have hk : Squarefree k := hm.of_mul_right.of_mul_right
    have hpk : ¬(p : ℤ) ∣ k := fun h =>
      not_dvd_of_squarefree_mul hpp hm (dvd_mul_of_dvd_right h _)
    have hqk : ¬(q : ℤ) ∣ k := not_dvd_of_squarefree_mul hqq hm.of_mul_right
    have hkp : legendreSym p k = -1 := by
      have := legendreSym_eq_one_of_ne (fun h => hpk ((Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd
        h |>.resolve_left (not_dvd_of_prime_ne hpp hqq hpq))) (h1' (q * k) rfl)
      rw [legendreSym.mul, hqp] at this
      linear_combination -this
    have hkq : legendreSym q k = -1 := by
      have := legendreSym_eq_one_of_ne (fun h => hqk ((Nat.prime_iff_prime_int.mp hqq).dvd_or_dvd
        h |>.resolve_left hqp')) (h2' (p * k) (by ring))
      rw [legendreSym.mul, legendreSym.quadratic_reciprocity_one_mod_four hp hq, hqp] at this
      linear_combination -this
    obtain ⟨X, Y, Z, h⟩ := lemma_two_if_dvd_both hp hq hqp hpq hk hpk hqk hkp hkq
    exact ⟨X, Y, Z, by rw [h]; push_cast; ring⟩
  · obtain ⟨k, rfl⟩ := hpm
    have hpk := not_dvd_of_squarefree_mul hpp hm
    have hqk : ¬(q : ℤ) ∣ k := fun h => hqm (dvd_mul_of_dvd_right h _)
    obtain ⟨X, Y, Z, h⟩ := lemma_two_if_dvd_left hp hq hm.of_mul_right hpk hqk
      (legendreSym_eq_one_of_ne hpk (h1' k rfl))
    exact ⟨X, Y, Z, by rw [h]; push_cast; ring⟩
  · obtain ⟨k, rfl⟩ := hqm
    have hqk := not_dvd_of_squarefree_mul hqq hm
    have hpk : ¬(p : ℤ) ∣ k := fun h => hpm (dvd_mul_of_dvd_right h _)
    obtain ⟨X, Y, Z, h⟩ := lemma_two_if_dvd_right hp hq hpq hm.of_mul_right hpk hqk
      (legendreSym_eq_one_of_ne hqk (h2' k rfl))
    exact ⟨X, Y, Z, by rw [h]; push_cast; ring⟩
  · exact lemma_two_if_coprime hp hq hpq hm hpm hqm

/-- **Robinson's Lemma 2.** Let `p` and `q` be odd primes with `p ≡ 1 (mod 4)` and
`(q / p) = -1`, and let `M` be a nonzero rational number. Then `X ^ 2 + q Y ^ 2 - p Z ^ 2 = M`
has a solution in rational numbers `X, Y, Z` if and only if `M` is of neither of the forms
`p k S ^ 2` with `(k / p) = -1` and `q k S ^ 2` with `(k / q) = -1`, where `k` is an integer and
`S` a rational number. (That `p` is odd follows from `p ≡ 1 (mod 4)`.)

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 2, p. 108: "If `p` and `q` are odd primes with `p ≡ 1 (mod 4)` and `(q/p) = −1`, then
`X² + qY² − pZ²` represents a nonzero rational number `M` if and only if `M` is not of the form
`pk·S²` with `(k/p) = −1` or `qk·S²` with `(k/q) = −1`." Capital letters denote rationals and small
letters integers (p. 106). Robinson states it without proof, as a special case of a theorem of
Hasse (p. 107). The "only if" half is `lemma_two_only_if`. For the "if" half, write
`M = m₀ S ^ 2` with `m₀` a squarefree integer; an auxiliary prime `r` from Dirichlet's theorem,
with `T = r` or `p r` according to `p ∣ m₀`, is represented both by `X ^ 2 + q Y ^ 2` and, by
Legendre's theorem, by a binary form attached to `m₀`. -/
theorem lemma_two {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1) (hq : q ≠ 2)
    (hqp : legendreSym p q = -1) {M : ℚ} (hM : M ≠ 0) :
    (∃ X Y Z : ℚ, X ^ 2 + q * Y ^ 2 - p * Z ^ 2 = M) ↔
      (¬∃ (k : ℤ) (S : ℚ), M = p * k * S ^ 2 ∧ legendreSym p k = -1) ∧
        ¬∃ (k : ℤ) (S : ℚ), M = q * k * S ^ 2 ∧ legendreSym q k = -1 :=
  ⟨lemma_two_only_if hp hq hqp hM, fun h => lemma_two_if hp hq hqp hM h.1 h.2⟩

end Rat.Robinson

end
