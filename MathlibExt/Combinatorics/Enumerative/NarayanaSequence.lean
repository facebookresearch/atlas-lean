/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Narayana's cows sequence

Formalizes the Narayana sequence from the Journal of Integer Sequences.
- Concept: `jis_sem_cf6cb7757b3800269bff893c` ("narayana sequence").
- Source statement: `jis_e95687510f34475587245fbb`.
- Source: `jis_source_f83f1af8a3d625820c162c43`
  (`https://cs.uwaterloo.ca/journals/JIS/VOL23/Das/bravo17.tex`).
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Narayana's cows sequence.** The sequence $(N_n)_{n \ge 0}$ of natural numbers defined by
$N_0 = 0$, $N_1 = N_2 = 1$ and $N_n = N_{n-1} + N_{n-3}$ for $n \ge 3$.

Source: concept `jis_sem_cf6cb7757b3800269bff893c`; source statement
`jis_e95687510f34475587245fbb` in source `jis_source_f83f1af8a3d625820c162c43`. -/
def narayanaCowsSequence : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ Nat.zero => Nat.succ Nat.zero
  | Nat.succ (Nat.succ Nat.zero) => Nat.succ Nat.zero
  | Nat.succ (Nat.succ (Nat.succ n)) =>
    narayanaCowsSequence (Nat.succ (Nat.succ n)) + narayanaCowsSequence n

end MetaMathlibExt
