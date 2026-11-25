/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Count

namespace MetaMathlibExt

@[expose] public section

/-- **Equilibrious binary words.** A finite word $u$ over the binary alphabet $\{0, 1\}$ is
equilibrious when the letters $0$ and $1$ occur the same number of times in $u$.

The letters $a$ and $b$ of the source alphabet $\Sigma = \{a, b\}$ are represented by $0$ and $1$.

Source: concept `jis_sem_061cc96760fa3a6b576dda00`,
source <https://cs.uwaterloo.ca/journals/JIS/VOL28/Coons/coons6.tex>, lines 543–575,
SHA-256 `409c8b4db7ce10e7f1cb6790bde41029c3667b383f6ccb05f6d374743bec2ff0`. -/
public def IsEquilibriousWord (u : List (Fin 2)) : Prop :=
  u.count 0 = u.count 1

/-- Decidability of the equilibrious-word predicate, by decidable equality on
the two `List.count` values. Exposed so `by decide` works across the module
boundary. Provenance: concept `jis_sem_061cc96760fa3a6b576dda00`, source
location `coons6.tex:543-575`. -/
public instance decidableIsEquilibriousWord (u : List (Fin 2)) :
    Decidable (IsEquilibriousWord u) := by
  unfold IsEquilibriousWord
  infer_instance

/-- **Reversal preserves equilibrious words.** A finite word $u$ over the binary alphabet
$\{0, 1\}$ is equilibrious if and only if its reversal is equilibrious.

Source: concept `jis_sem_061cc96760fa3a6b576dda00`, source location
`coons6.tex:543-575`. -/
public theorem isEquilibriousWord_reverse {u : List (Fin 2)} :
    IsEquilibriousWord u.reverse ↔ IsEquilibriousWord u := by
  unfold IsEquilibriousWord
  rw [List.count_reverse, List.count_reverse]

end

end MetaMathlibExt
