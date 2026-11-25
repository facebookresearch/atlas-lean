/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AP.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Arithmetic progressions with a common difference.** Let $G$ be an additive commutative
monoid and let $A$ and $B$ be finite subsets of $G$. We say that $A$ and $B$ are arithmetic
progressions with a common difference if there are $d, a, b \in G$ such that
$A = \{a + nd : n \in \mathbb{N},\ n < |A|\}$ and $B = \{b + nd : n \in \mathbb{N},\ n < |B|\}$,
where $nd$ is the sum of $n$ copies of $d$. The two progressions may have different initial terms
and different lengths.

Source: Fabián Arias, Jerson Borja, and Samuel Anaya, *Counting Integers
Representable as Sums of k-th Powers Modulo n*, Journal of Integer Sequences
26 (2023), Article 23.8.1, Theorem [Vosper] `theo_Vosper` condition (iii),
lines 256–267,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Borja/borja4.tex>:
"`A` and `B` are arithmetic progressions with the same common difference". -/
def AreFiniteArithmeticProgressionsWithCommonDifference {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A B : Finset G) : Prop :=
  ∃ d a b : G, (A : Set G).IsAPOfLengthWith A.card a d ∧
    (B : Set G).IsAPOfLengthWith B.card b d

end MetaMathlibExt
