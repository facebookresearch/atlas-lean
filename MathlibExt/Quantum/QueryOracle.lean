/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-!
# Quantum query oracle

The standard query oracle maps basis states
`|x, y>` to `|x, y XOR f x>`. This module models it on
`Fin n × Bool` and proves it is an involution, hence a
bijection, preserving the register value. The amplitude-level
unitary model is not formalized here.
-/

@[expose] public section

/-- Quantum query oracle on basis states (core of QCI-51):
`O_f |x, y> = |x, y XOR f x>`, modeled as a function on
`Fin n × Bool`. -/
def queryOracle {n : ℕ} (f : Fin n → Bool) (p : Fin n × Bool) : Fin n × Bool :=
  (p.1, if f p.1 then !p.2 else p.2)

/-- The oracle is an involution: querying twice restores the
basis state. -/
theorem queryOracle_involutive {n : ℕ} (f : Fin n → Bool) :
    Function.Involutive (queryOracle f) := by
  intro p
  cases h : f p.1 <;> simp [queryOracle, h]

/-- The oracle is a bijection (unitary at the basis level). -/
theorem queryOracle_bijective {n : ℕ} (f : Fin n → Bool) :
    Function.Bijective (queryOracle f) :=
  (queryOracle_involutive f).bijective

/-- The oracle preserves the register value `x`. -/
theorem queryOracle_fst {n : ℕ} (f : Fin n → Bool) (p : Fin n × Bool) :
    (queryOracle f p).1 = p.1 :=
  rfl

end
