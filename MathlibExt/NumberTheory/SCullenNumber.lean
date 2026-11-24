/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **The $s$-Cullen value.** For natural numbers $s$ and $n$, the $s$-Cullen value is
$C_{n,s} = n s^n + 1$.

Source: Jon Grantham and Hester Graves, *The abc Conjecture Implies That Only Finitely Many
s-Cullen Numbers Are Repunits*, Journal of Integer Sequences 24 (2021),
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Grantham/gran4.tex>.

JIS concept: `jis_sem_281a433c6542caee86b48369`; defining statement:
`jis_0272eab809344ae92672f303`.
-/
def sCullenNumber (s n : ℕ) : ℕ := n * s ^ n + 1

/-- **$s$-Cullen numbers.** For natural numbers $s$ and $n$, write $C_{n,s} = n s^n + 1$ for the
$s$-Cullen value. A natural number $m$ is an $s$-Cullen number when $s \ge 2$ and $m = C_{n,s}$
for some natural number $n \ge 1$.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Grantham/gran4.tex>.
-/
def IsSCullenNumber (s m : ℕ) : Prop :=
  2 ≤ s ∧ ∃ n, 0 < n ∧ sCullenNumber s n = m

end


end MetaMathlibExt
