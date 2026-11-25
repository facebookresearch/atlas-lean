/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Notation

/-!
# Diophantine quintuple conjecture (1)

No Diophantine quintuple exists.
-/

namespace MathlibExt.NumberTheory.DiophantineQuintupleConjectureQuestion1Wanted

/-- **Diophantine tuples.** A finite set $s$ of natural numbers is a Diophantine tuple when every
element of $s$ is positive and, for all $a, b \in s$ with $a < b$, the number $ab + 1$ is a perfect
square.

Source: OPG-16555 (Diophantine quintuple conjecture) [OpenGarden]. -/
def IsDiophantineTuple (s : Finset ℕ) : Prop :=
  (∀ a ∈ s, 0 < a) ∧ ∀ a ∈ s, ∀ b ∈ s, a < b → IsSquare (a * b + 1)

/-- **The statement that no Diophantine quintuple exists.** The proposition that no finite set of
natural numbers with exactly five elements is a Diophantine tuple, that is, that there is no
Diophantine quintuple.

Source: OPG-16555 (Diophantine quintuple conjecture) [OpenGarden]. -/
def Statement : Prop :=
  ¬∃ s : Finset ℕ, s.card = 5 ∧ IsDiophantineTuple s

/--
**There is no Diophantine quintuple.** The statement that no Diophantine quintuple exists holds:
no finite set of natural numbers with exactly five elements is a Diophantine tuple.

This was an open conjecture, resolved by He, Togbé, and Ziegler.

Source: Bo
He, Alain Togbé, and Volker Ziegler, There is no Diophantine quintuple, Transactions of the
American Mathematical Society 371 (2019), 6665–6709, https://doi.org/10.1090/tran/7573. Moved
from `OpenConjectures/NumberTheory/DiophantineQuintupleConjectureQuestion1`.
-/
theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.DiophantineQuintupleConjectureQuestion1Wanted
