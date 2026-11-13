/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Palindromic Narayana numbers

This file defines the palindromic Narayana numbers appearing in Paul Barry,
*Generalized Catalan Numbers Associated with a Family of Pascal-like Triangles*:
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry3/barry422.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Palindromic Narayana numbers.** For natural numbers $n$ and $k$, the palindromic Narayana
number is the rational number $\tilde{N}(n, k) = \binom{n}{k} \binom{n+1}{k} / (k+1)$.

The value is taken in $\mathbb{Q}$ so that the displayed quotient is represented literally.

Source: Paul Barry, "Generalized Catalan Numbers Associated with a Family of Pascal-like
Triangles," <https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry3/barry422.tex>.
-/
def palindromicNarayanaNumber (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * ((n + 1).choose k : ℚ) / (k + 1 : ℚ)

end MetaMathlibExt
