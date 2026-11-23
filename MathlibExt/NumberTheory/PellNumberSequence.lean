/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Pell numbers

This module defines the classical Pell number sequence. It is distinct from the parametrized
Pell-equation solution sequences in `Mathlib.NumberTheory.PellMatiyasevic`.

JIS concept: `jis_sem_39440c502b73b93425e3ad17`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Pell numbers.** The Pell numbers $P_n$, for natural numbers $n$, are defined by $P_0 = 0$,
$P_1 = 1$ and $P_{n+2} = 2P_{n+1} + P_n$ for every $n$. They begin $0, 1, 2, 5, 12, \dots$

Sources:
* Tian-Xiao He, *Impulse Response Sequences and Construction of Number Sequence Identities*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL16/He/he13.tex>.
* Tian-Xiao He and Peter J.-S. Shiue, *An Approach to the Construction of Linear Divisibility
  Sequences of Higher Orders*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL20/He/he59.tex>.
-/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pellNumber (n + 1) + pellNumber n

end

end MetaMathlibExt
