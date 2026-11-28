/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DNF satisfaction: definitions
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# DNF satisfaction: definitions

Satisfaction of a formula in disjunctive normal form (`dnfSat`), given as a list of terms, each a
list of literals `(variable, polarity)`. This is the definition that the statements of
`WantedExt.Complexity.KeyTheorems.KarpLubyWanted`, and of the wanted modules built on it, use,
moved here unchanged (name included) so that their proofs can import it.

Source: R. M. Karp and M. Luby, "Monte-Carlo algorithms for enumeration and reliability problems",
Proceedings of the Twenty-Fourth Annual Symposium on Foundations of Computer Science (FOCS 1983),
56-64.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.KarpLuby

/-- **Satisfaction of a DNF formula.** A DNF formula is a list of terms, each a list of literals
$(v, b)$ of a natural number $v$ (the variable) and a boolean $b$ (the polarity). An assignment $a$
of booleans to the natural numbers satisfies the formula when some term of it has $a(v) = b$ for
every literal $(v, b)$ of that term. -/
def dnfSat (assign : ℕ → Bool) (φ : List (List (ℕ × Bool))) : Prop :=
  ∃ term ∈ φ, ∀ p ∈ term, assign p.1 = p.2

end MetaMathlibExt.Complexity.KeyTheorems.KarpLuby
