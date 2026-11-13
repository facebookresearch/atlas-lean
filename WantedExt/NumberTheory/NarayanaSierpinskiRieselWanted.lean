/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import WantedExt.NumberTheory.SierpinskiRieselRepdigitsWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Narayana numbers that are Riesel numbers.** Let $(N_t)$ be Narayana's cows sequence, with
$N_0 = 0$ and $N_1 = N_2 = 1$. If $t$ is congruent modulo $718391520$ to one of the $27$ residues
$3629412$, $13386852$, $73151172$, $96325092$, $101203812$, $119499012$, $175604292$,
$198778212$, $212194692$, $240247332$, $268299972$, $328064292$, $337821732$, $360995652$,
$384169572$, $402464772$, $425638692$, $467107812$, $476865252$, $495160452$, $564682212$,
$587856132$, $592734852$, $611030052$, $629325252$, $652499172$, $703725732$, then $N_t$ is a
Riesel number: $N_t$ is odd and $N_t \cdot 2^n - 1$ is not prime for every $n \ge 1$.

With this indexing, $N_t$ is odd exactly when $t \bmod 7 \in \{1, 2, 3, 5\}$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 2 (`integers-2024-A10-thm-2`). -/
public theorem_wanted isRieselNumber_narayanaCowsSequence {t : ℕ}
    (ht : t % 718391520 ∈ ({3629412, 13386852, 73151172, 96325092, 101203812, 119499012,
      175604292, 198778212, 212194692, 240247332, 268299972, 328064292, 337821732, 360995652,
      384169572, 402464772, 425638692, 467107812, 476865252, 495160452, 564682212, 587856132,
      592734852, 611030052, 629325252, 652499172, 703725732} : Finset ℕ)) :
    IsRieselNumber (narayanaCowsSequence t)

/-- **Infinitely many Narayana numbers are Sierpiński numbers.** There are infinitely many
natural numbers $k$ that are Sierpiński numbers and terms of Narayana's cows sequence $(N_t)$,
that is, $k = N_t$ for some $t$; here a Sierpiński number is an odd $k$ such that
$k \cdot 2^n + 1$ is not prime for every $n \ge 1$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 3 (`integers-2024-A10-thm-3`). -/
public theorem_wanted infinite_setOf_isSierpinskiNumber_narayanaCowsSequence :
    {k : ℕ | IsSierpinskiNumber k ∧ ∃ t, narayanaCowsSequence t = k}.Infinite

end

end MetaMathlibExt
