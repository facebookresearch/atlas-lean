/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Column weights

This definition is used by Dominik Beck, Zelin Lv, and Aaron Potechin,
*The Sixth Moment of Random Determinants*, Journal of Integer Sequences 26
(2023), Article 23.6.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Lv/lv3.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Column weight.** Let $n$ be a natural number, $M$ a commutative monoid and
$f \colon \mathbb{N} \to M$ a function. A column is a finite list of entries from
$\{0, 1, \dots, n - 1\}$; for each $j$ in this range let $c_j$ be the number of times $j$ occurs
in the column. The weight of the column is the product $\prod_{j=0}^{n-1} f(c_j)$ in $M$.

Source: Dominik Beck, Zelin Lv, and Aaron Potechin, *The Sixth Moment of Random
Determinants*, Journal of Integer Sequences 26 (2023), Article 23.6.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Lv/lv3.tex>. Stable source identifiers:
concept `jis_sem_a5942561d609e6dce822e138`, statement `jis_7896cefc507363fdee018052`.
-/
def columnWeight (n : ℕ) {M : Type*} [CommMonoid M]
    (factor : ℕ → M) (column : List (Fin n)) : M :=
  ∏ j, factor ((column.filter (· = j)).length)

end

end MetaMathlibExt
