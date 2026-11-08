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

/-- Theorem 2: if `t ≡ x (mod 718391520)` for one of the 27 listed residues `x`, then the
Narayana cows number `N_t` is a Riesel number (an "NC-Riesel number": a Riesel number that is a
term of Narayana's cows sequence). Riesel number is the standard notion
(`IsRieselNumber`: odd `k` with `k·2^n - 1` composite for all `n ≥ 1`), and `N_t` is
`narayanaCowsSequence t` (`N_0 = 0`, `N_1 = N_2 = 1`); this indexing matches the record's
residue data `I(1, 2) (mod 7) = {1, 2, 3, 5}` (`N_t` is odd exactly for those `t mod 7`).

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 2 (`integers-2024-A10-thm-2`). -/
public theorem_wanted isRieselNumber_narayanaCowsSequence {t : ℕ}
    (ht : t % 718391520 ∈ ({3629412, 13386852, 73151172, 96325092, 101203812, 119499012,
      175604292, 198778212, 212194692, 240247332, 268299972, 328064292, 337821732, 360995652,
      384169572, 402464772, 425638692, 467107812, 476865252, 495160452, 564682212, 587856132,
      592734852, 611030052, 629325252, 652499172, 703725732} : Finset ℕ)) :
    IsRieselNumber (narayanaCowsSequence t)

/-- Theorem 3: there are infinitely many NC-Sierpiński numbers, i.e. infinitely many terms of
Narayana's cows sequence are Sierpiński numbers (`IsSierpinskiNumber`: odd `k` with
`k·2^n + 1` composite for all `n ≥ 1`).

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 3 (`integers-2024-A10-thm-3`). -/
public theorem_wanted infinite_setOf_isSierpinskiNumber_narayanaCowsSequence :
    {k : ℕ | IsSierpinskiNumber k ∧ ∃ t, narayanaCowsSequence t = k}.Infinite

end

end MetaMathlibExt
