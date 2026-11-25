/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots

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

end

end MetaMathlibExt
