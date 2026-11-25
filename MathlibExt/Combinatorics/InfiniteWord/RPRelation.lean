/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Basic

namespace MetaMathlibExt

@[expose] public section

namespace ReversePermute

/-- **$k$-strings.** For a natural number $k$, a $k$-string is a finite sequence (possibly empty)
of elements of $\{0, 1, \ldots, k-1\}$.

Source: statement `jis_cd98d66d9dff78260169a2e4` for concept
`jis_sem_f50f75500661653b133949f3` (`rp relation`, alias `RP relation`). -/
public abbrev KString (k : ℕ) := List (Fin k)

/-- **The reverse-permute relation.** For a natural number $k$, a $k$-string $s$ is related to a
$k$-string $t$ by the reverse-permute (RP) relation when there is a permutation $\sigma$ of
$\{0, 1, \ldots, k-1\}$ such that $t$ is obtained, either from $s$ or from the reversal of $s$,
by replacing each entry $x$ with $\sigma(x)$.

Source: concept `jis_sem_f50f75500661653b133949f3` (`rp relation`, alias `RP relation`) and
source statement `jis_cd98d66d9dff78260169a2e4`. -/
public def rpRelation (k : ℕ) (s t : KString k) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), t = s.map (⇑σ) ∨ t = s.reverse.map (⇑σ)

end ReversePermute

end

end MetaMathlibExt
