/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic

/-!
# Quantum query oracle

The standard query oracle maps basis states `|x, y⟩` to `|x, y ⊕ f x⟩`. This module models
it as a function on the basis labels `Fin n × Bool`, proves that it flips the target bit
exactly when `f x = true` (`queryOracle_apply`), and that it is an involution, hence a
bijection of the basis labels, preserving the register value. The amplitude-level unitary
operator is not formalized here.
-/

@[expose] public section

namespace Cslib.Quantum

/-- The query oracle on basis states, `O_f |x, y⟩ = |x, y ⊕ f x⟩`, modeled as a function on
`Fin n × Bool`. -/
def queryOracle {n : ℕ} (f : Fin n → Bool) (p : Fin n × Bool) : Fin n × Bool :=
  (p.1, if f p.1 then !p.2 else p.2)

/-- The oracle XORs the target bit with `f x`. -/
theorem queryOracle_apply {n : ℕ} (f : Fin n → Bool) (x : Fin n) (y : Bool) :
    queryOracle f (x, y) = (x, xor y (f x)) := by
  cases h : f x <;> simp [queryOracle, h]

/-- The oracle is an involution: querying twice restores the basis state. -/
theorem queryOracle_involutive {n : ℕ} (f : Fin n → Bool) :
    Function.Involutive (queryOracle f) := by
  intro p
  cases h : f p.1 <;> simp [queryOracle, h]

/-- The oracle is a bijection of the basis labels. -/
theorem queryOracle_bijective {n : ℕ} (f : Fin n → Bool) :
    Function.Bijective (queryOracle f) :=
  (queryOracle_involutive f).bijective

/-- The oracle preserves the register value `x`. -/
theorem queryOracle_fst {n : ℕ} (f : Fin n → Bool) (p : Fin n × Bool) :
    (queryOracle f p).1 = p.1 :=
  rfl

end Cslib.Quantum

end
