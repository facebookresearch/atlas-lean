/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

/-! # Kimberling's blocks

We define Kimberling's binary morphism and its blocks and prove the four-block concatenation
recurrence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Kimberling's morphism.** Kimberling's morphism $h$ sends each letter of the alphabet
$\{0, 1\}$ to a finite word over $\{0, 1\}$, by $h(1) = 110$ and $h(0) = 11$.

The letters $0$ and $1$ are represented by the Boolean values false and true.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1 and Section 2 (the morphism `h`). -/
public def kimberlingMorphism : Bool → List Bool
  | true => [true, true, false]
  | false => [true, true]

/-- **Kimberling's blocks.** Let $h$ be Kimberling's morphism on the alphabet $\{0, 1\}$, given by
$h(1) = 110$ and $h(0) = 11$ and extended to finite words by concatenation. For each natural
number $n$, the $n$-th Kimberling block is the finite word $K_n = h^n(1)$, the $n$-th iterate of
$h$ applied to the one-letter word $1$. Thus $K_0 = 1$, $K_1 = 110$ and $K_2 = 11011011$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2 (`K_n = h^n(1)`). -/
public def kimberlingBlock (n : ℕ) : List Bool :=
  morphIterate kimberlingMorphism n [true]

/-- **Recursive structure of Kimberling's blocks.** Let $h$ be Kimberling's morphism on $\{0, 1\}$,
$h(1) = 110$ and $h(0) = 11$, and let $K_n = h^n(1)$. Then for every $n \ge 2$,
$K_n = K_{n-1} K_{n-1} K_{n-2} K_{n-2}$ (concatenation of words).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Proposition 1 (`integers-2024-A51-prop-1`). -/
public theorem kimberlingBlock_eq_append {n : ℕ} (hn : 2 ≤ n) :
    kimberlingBlock n = kimberlingBlock (n - 1) ++ kimberlingBlock (n - 1) ++
      kimberlingBlock (n - 2) ++ kimberlingBlock (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  change kimberlingBlock (k + 2) =
    kimberlingBlock (k + 1) ++ kimberlingBlock (k + 1) ++ kimberlingBlock k ++ kimberlingBlock k
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [morphExtend_append] using! congrArg (morphExtend kimberlingMorphism) ih

end

end MetaMathlibExt
