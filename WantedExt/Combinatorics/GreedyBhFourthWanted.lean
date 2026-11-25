/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The fourth positive element in the greedy `B_h`-set

Statements from Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth
Positive Element in the Greedy `B_h`-Set", *Journal of Integer
Sequences* 27 (2024), Article 24.7.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/OBryant2/obryant4.html>).

The greedy choice is expressed stage by stage with MathlibExt's
canonical `AdditiveCombinatorics.IsBhSet`, using the paper's known
terms `a₀(h) = 0`, `a₁(h) = 1`, `a₂(h) = h + 1`, and
`a₃(h) = h² + h + 1`.

This module imports `MathlibExt.Combinatorics.GreedyBhFourth`, which
proves the upper and lower bounds for the fourth greedy term. The formula
for the fourth term remains a wanted statement here.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.GreedyBhFourth

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.GreedyBhFourthWanted

/-- **Formula for the fourth greedy $B_h$ term.** For every integer $h \ge 1$, the fourth positive
element $a_4(h)$ of the greedy $B_h$-set is $(h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and
$(h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Theorem 1. -/
theorem_wanted isFourthGreedyBh_fourthValue
    (h : ℕ) (hh : 0 < h) :
    IsFourthGreedyBh h (fourthValue h)

end MathlibExt.Combinatorics.GreedyBhFourthWanted
