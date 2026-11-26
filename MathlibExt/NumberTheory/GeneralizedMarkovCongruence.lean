/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Ring

/-!
# The congruence $x^2 + kx + 1 \equiv 0 \pmod b$

The number of solutions of $x^2 + kx + 1 \equiv 0 \pmod b$ with $0 \le x < b$ controls the
uniqueness of generalized Markov triples with maximum $b$ (Gyoda and Maruyama, *Uniqueness
Theorem of Generalized Markov Numbers That Are Prime Powers*, INTEGERS 26 (2026), Article A91,
Theorem 1.5). This file defines that number and proves that it is at most two when $b$ is a
prime: modulo a prime, the quadratic $x^2 + kx + 1$ has at most two roots.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Number of solutions of $x^2 + kx + 1 \equiv 0 \pmod b$.** For natural numbers $k$ and
$b$, this is the number of integers $x$ with $0 \le x < b$ such that $b$ divides
$x^2 + kx + 1$. For $b = 0$ it is $0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.5. -/
public def genMarkovCongruenceCount (k b : ℕ) : ℕ :=
  ((range b).filter fun x => b ∣ x ^ 2 + k * x + 1).card

/-- **The congruence $x^2 + 1 \equiv 0 \pmod 5$ has two solutions.** Exactly two integers $x$
with $0 \le x < 5$ satisfy $x^2 + 1 \equiv 0 \pmod 5$.

They are $x = 2$ and $x = 3$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.2. -/
public theorem genMarkovCongruenceCount_zero_five : genMarkovCongruenceCount 0 5 = 2 := by
  decide

open Polynomial in
/-- **At most two solutions of $x^2 + kx + 1 \equiv 0$ modulo a prime.** For every prime $p$
and every $k \in \mathbb{N}$, at most two integers $x$ with $0 \le x < p$ satisfy
$x^2 + kx + 1 \equiv 0 \pmod p$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.9. -/
public theorem genMarkovCongruenceCount_prime_le_two {p : ℕ} (hp : p.Prime) (k : ℕ) :
    genMarkovCongruenceCount k p ≤ 2 := by
  have := Fact.mk hp
  set S := (range p).filter fun x => p ∣ x ^ 2 + k * x + 1 with hS
  -- The solutions are roots of the monic quadratic `X ^ 2 + k X + 1` over the field `ZMod p`.
  set f : (ZMod p)[X] := C 1 * X ^ 2 + C (k : ZMod p) * X + C 1 with hf
  have hdeg : f.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hf0 : f ≠ 0 := fun h => by simp [h] at hdeg
  -- Reduction modulo `p` is injective on `range p`.
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) S := by
    intro x hx y hy hxy
    simp only [hS, coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at hxy
  calc genMarkovCongruenceCount k p = (S.image (Nat.cast : ℕ → ZMod p)).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ f.natDegree := by
        refine card_le_degree_of_subset_roots fun z hz => ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.mp (mem_val.mp hz)
        have hx0 : ((x ^ 2 + k * x + 1 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr (mem_filter.mp hx).2
        push_cast at hx0
        rw [mem_roots hf0, IsRoot.def, hf]
        simpa using hx0
    _ = 2 := hdeg

/-- **At most two solutions of $x^2 + kx + 1 \equiv 0$ modulo an odd prime power.** Let $p$
be an odd prime, let $m \ge 2$ and let $k \in \mathbb{N}$ with $k^2 - 4 \not\equiv 0 \pmod p$.
Then at most two integers $x$ with $0 \le x < p^m$ satisfy
$x^2 + kx + 1 \equiv 0 \pmod{p^m}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.11. -/
public theorem genMarkovCongruenceCount_prime_pow_le_two {p m k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hk : ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4) :
    genMarkovCongruenceCount k (p ^ m) ≤ 2 := by
  have hpPos : 0 < p := Nat.zero_lt_two.trans (lt_of_le_of_ne hp.two_le hp2.symm)
  have hpm : p ∣ p ^ m := dvd_pow_self p (by omega)
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  unfold genMarkovCongruenceCount
  refine (card_le_card_of_injOn (· % p) ?_ ?_).trans
    (genMarkovCongruenceCount_prime_le_two hp k)
  · intro x hx
    obtain ⟨_, hxroot⟩ := mem_filter.mp hx
    have hmod := Nat.mod_modEq x p
    have hroot := ((hmod.pow 2).add (hmod.mul_left k)).add_right 1
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hpPos),
      Nat.modEq_zero_iff_dvd.mp (hroot.trans (Nat.modEq_zero_iff_dvd.mpr (hpm.trans hxroot)))⟩
  · intro x hx y hy hxy
    obtain ⟨hxlt, hxroot⟩ := mem_filter.mp hx
    obtain ⟨hylt, hyroot⟩ := mem_filter.mp hy
    have hd : (p : ℤ) ∣ (y : ℤ) - x := Nat.modEq_iff_dvd.mp hxy
    have hcast {z : ℕ} (hz : p ^ m ∣ z ^ 2 + k * z + 1) :
        (p : ℤ) ^ m ∣ (z : ℤ) ^ 2 + k * z + 1 := by
      exact_mod_cast hz
    -- If p divided both factors, it would divide 2x + k and hence the discriminant.
    have hsum : ¬ (p : ℤ) ∣ (x : ℤ) + y + k := by
      intro hs
      have hderiv : (p : ℤ) ∣ 2 * (x : ℤ) + k := by
        convert dvd_sub hs hd using 1
        ring
      have hxmod : (p : ℤ) ∣ (x : ℤ) ^ 2 + k * x + 1 :=
        (show (p : ℤ) ∣ (p : ℤ) ^ m by exact_mod_cast hpm).trans (hcast hxroot)
      apply hk
      calc
        (p : ℤ) ∣ (2 * (x : ℤ) + k) ^ 2 - 4 * ((x : ℤ) ^ 2 + k * x + 1) :=
          dvd_sub (dvd_pow hderiv (by decide)) (dvd_mul_of_dvd_right hxmod _)
        _ = (k : ℤ) ^ 2 - 4 := by ring
    have hprod : (p : ℤ) ^ m ∣ ((y : ℤ) - x) * ((x : ℤ) + y + k) := by
      convert dvd_sub (hcast hyroot) (hcast hxroot) using 1
      ring
    have hdiff := hpInt.pow_dvd_of_dvd_mul_right m hsum hprod
    have hmod : Nat.ModEq (p ^ m) x y := Nat.modEq_iff_dvd.mpr (by exact_mod_cast hdiff)
    exact hmod.eq_of_lt_of_lt (mem_range.mp hxlt) (mem_range.mp hylt)

end

end MetaMathlibExt
