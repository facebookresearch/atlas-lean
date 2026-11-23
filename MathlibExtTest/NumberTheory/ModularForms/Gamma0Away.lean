/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.Gamma0Away

@[expose] public section

open Matrix

open scoped MatrixGroups

namespace Ihara

-- Characterization consumer with the original binders.
example (N q : ℕ) (g : SL(2, ZAway q)) :
    g ∈ Gamma0Away N q ↔ (N : ZAway q) ∣ g 1 0 :=
  mem_Gamma0Away

-- The identity lies in `Γ₀(N)` over `ℤ[1/q]`, and its character is `1`.
example (N q : ℕ) : (1 : SL(2, ZAway q)) ∈ Gamma0Away N q := by
  rw [mem_Gamma0Away]
  simp

example (N q : ℕ) (hNq : Nat.Coprime N q) :
    gamma0AwayUnitsChar N q hNq 1 = 1 :=
  map_one _

-- Nontrivial instance: `N = 5`, `q = 2` are coprime, the two vertex
-- compositions agree with the integral character, as a function equality.
example (h : Nat.Coprime 5 2) (g : CongruenceSubgroup.Gamma0 5) :
    gamma0AwayUnitsChar 5 2 h (vertexZeroAway 5 2 g) = gamma0UnitsHom 5 g := by
  have := gamma0AwayUnitsChar_comp_vertexZeroAway 5 2 h
  exact MonoidHom.ext_iff.mp this g

example (h : Nat.Coprime 5 2) (g : CongruenceSubgroup.Gamma0 5) :
    gamma0AwayUnitsChar 5 2 h (vertexOneAway 5 2 g) = gamma0UnitsHom 5 g := by
  have := gamma0AwayUnitsChar_comp_vertexOneAway 5 2 h
  exact MonoidHom.ext_iff.mp this g

-- The conjugation equivalence fixes the identity.
example (q : ℕ) : wConj q 1 = 1 := map_one _

end Ihara
