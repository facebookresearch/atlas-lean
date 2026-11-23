/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith

/-!
# Solutions of `3^x + 35^y = z^2`

The ATLAS wiki attributes this classification to Suton Tadee's “On the Diophantine Equation
$n^x + (5p)^y = z^2$”. When both exponents are positive, we rule out solutions modulo $60$.
When one exponent vanishes, we factor $z^2 - 1$.
-/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

private lemma pos_pow_mem {a : ZMod 60} {s : Finset (ZMod 60)} (ha : a ∈ s)
    (hs : ∀ r ∈ s, r * a ∈ s) (n : ℕ) : a ^ (n + 1) ∈ s := by
  induction n with
  | zero => simpa using ha
  | succ n ih => exact pow_succ a (n + 1) ▸ hs _ ih

private lemma no_pos_exponents (x y z : ℕ) :
    3 ^ (x + 1) + 35 ^ (y + 1) ≠ z ^ 2 := by
  let s : Finset (ZMod 60) := {3, 9, 27, 21}
  let t : Finset (ZMod 60) := {35, 25}
  have hx : (3 : ZMod 60) ^ (x + 1) ∈ s := pos_pow_mem (by decide) (by decide) x
  have hy : (35 : ZMod 60) ^ (y + 1) ∈ t := pos_pow_mem (by decide) (by decide) y
  have hmod : ∀ a ∈ s, ∀ b ∈ t, ∀ r : ZMod 60, a + b ≠ r ^ 2 := by
    simp only [s, t, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    decide
  intro h
  apply hmod _ hx _ hy (z : ZMod 60)
  simpa using congrArg (Nat.cast : ℕ → ZMod 60) h

/-- In the factorization $(z-1)(z+1) = a p^n$, the odd prime power divides one factor
and is thus at most $z+1$. Cancelling it gives $z-1 \le a$. -/
private lemma prime_pow_le_cofactor_add_two {p a n z : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (ha : 0 < a) (h : a * p ^ n + 1 = z ^ 2) : p ^ n ≤ a + 2 := by
  have hpos := Nat.mul_pos ha (pow_pos hp.pos n)
  obtain _ | k := z
  · simp at h
  have hfac : k * (k + 2) = a * p ^ n := by nlinarith only [h]
  have hk : 0 < k := Nat.pos_of_mul_pos_right (hfac.symm ▸ hpos)
  have hdvd : p ^ n ∣ k * (k + 2) := hfac ▸ dvd_mul_left _ _
  have hle : p ^ n ≤ k + 2 := by
    by_cases hpk : p ∣ k
    · have hnd : ¬p ∣ k + 2 := fun hd =>
        (Nat.not_dvd_of_pos_of_lt (by decide) hp2) ((Nat.dvd_add_right hpk).mp hd)
      exact (Nat.le_of_dvd hk (hp.prime.pow_dvd_of_dvd_mul_right n hnd hdvd)).trans (by omega)
    · exact Nat.le_of_dvd (by omega) (hp.prime.pow_dvd_of_dvd_mul_left n hpk hdvd)
  have hmul := Nat.mul_le_mul_left k hle
  rw [hfac] at hmul
  have hka := Nat.le_of_mul_le_mul_right hmul (pow_pos hp.pos n)
  omega

/-- If the larger factor is prime and exceeds the smaller by at least two, only the
first power of their product can be one less than a square. -/
private lemma exp_eq_one {a p n z : ℕ} (ha : 0 < a) (hp : p.Prime) (hgap : a + 2 ≤ p)
    (h : (a * p) ^ n + 1 = z ^ 2) : n = 1 := by
  rcases n with _ | _ | n
  · exact (Nat.prime_two.prime.not_isSquare ⟨z, by simpa [sq] using h⟩).elim
  · rfl
  · rw [mul_pow] at h
    have hle := prime_pow_le_cofactor_add_two hp (by omega) (pow_pos ha _) h
    rw [pow_succ, pow_succ a] at hle
    have hlt : a ^ (n + 1) < p ^ (n + 1) := Nat.pow_lt_pow_left (by omega) (by omega)
    -- Multiplying by the larger base makes the gap between the powers exceed two.
    have h₁ := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hlt)
    have h₂ := Nat.mul_le_mul_left (a ^ (n + 1)) (show a ≤ p by omega)
    rw [Nat.succ_mul] at h₁
    omega

/-- The natural solutions of $3^x + 35^y = z^2$ are $(1,0,2)$ and $(0,1,6)$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 4. -/
public theorem three_pow_add_thirtyfive_pow (x y z : ℕ) :
    3 ^ x + 35 ^ y = z ^ 2 ↔
      (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 6) := by
  constructor
  · intro h
    match x, y with
    | 0, y =>
      have hy : y = 1 := exp_eq_one (a := 5) (p := 7) (by decide) (by decide) (by decide)
        (by simpa [add_comm] using h)
      subst y
      exact Or.inr ⟨rfl, rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) h.symm⟩
    | x, 0 =>
      have hx : x = 1 := exp_eq_one (a := 1) (p := 3) (by decide) (by decide) (by decide)
        (by simpa using h)
      subst x
      exact Or.inl ⟨rfl, rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) h.symm⟩
    | x + 1, y + 1 => exact (no_pos_exponents x y z h).elim
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> decide

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
