/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Kneser p-neighbors

This module defines the symmetric `p`-neighbor relation for two lattices
represented as submodules of a common ambient module.
-/

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **$p$-neighbors of submodules.** Let $R$ be a commutative ring, $M$ an $R$-module and $p$ a
natural number. Two submodules $L_1$ and $L_2$ of $M$ are $p$-neighbors when $p$ is prime and the
intersection $L_1 \cap L_2$ has index $p$ in each of them, that is, the quotients
$L_1 / (L_1 \cap L_2)$ and $L_2 / (L_1 \cap L_2)$ both have exactly $p$ elements. -/
def ArePNeighbors (p : ℕ) (L₁ L₂ : Submodule R M) : Prop :=
  Nat.Prime p ∧
    Nat.card (L₁ ⧸ Submodule.comap L₁.subtype (L₁ ⊓ L₂)) = p ∧
    Nat.card (L₂ ⧸ Submodule.comap L₂.subtype (L₁ ⊓ L₂)) = p

/-- **The $p$-neighbor relation is symmetric.** For every natural number $p$ and all submodules
$L_1$, $L_2$ of a module $M$ over a commutative ring $R$, $L_1$ and $L_2$ are $p$-neighbors if
and only if $L_2$ and $L_1$ are $p$-neighbors. -/
theorem arePNeighbors_comm (p : ℕ) (L₁ L₂ : Submodule R M) :
    ArePNeighbors p L₁ L₂ ↔ ArePNeighbors p L₂ L₁ := by
  unfold ArePNeighbors
  rw [inf_comm]
  aesop

/-- **No submodules are $1$-neighbors.** For any submodules $L_1$ and $L_2$ of a module $M$
over a commutative ring $R$, $L_1$ and $L_2$ are not $1$-neighbors, since $1$ is not prime. -/
theorem not_arePNeighbors_one (L₁ L₂ : Submodule R M) :
    ¬ArePNeighbors 1 L₁ L₂ := by
  intro h
  exact Nat.not_prime_one h.1

end Submodule
