/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovEvenParameter

/-! # Tests for even generalized Markov numbers -/

open MetaMathlibExt

-- The classical case includes the triple `(1, 2, 1)`.
example : Even (0 : ℕ) :=
  even_of_even_genMarkovNumber ⟨1, 1, by unfold IsGenMarkovTriple; decide⟩ (by decide : Even 2)

-- The even entry need not be the maximum of the triple.
example : Even (2 : ℕ) :=
  even_of_even_genMarkovNumber ⟨1, 25, by unfold IsGenMarkovTriple; decide⟩ (by decide : Even 4)

-- An odd parameter cannot admit an even number.
example : ¬ IsGenMarkovNumber 1 2 := fun h =>
  (by decide : ¬ Even (1 : ℕ)) (even_of_even_genMarkovNumber h (by decide))
