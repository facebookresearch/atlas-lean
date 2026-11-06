/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic

/-!
# First differences of binary words

This file formalizes the first-difference operation from Ricardo Astudillo,
*On a Class of Thue-Morse Type Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Astudillo/astudillo12.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **First difference of an infinite binary word.** For an infinite word $w = w_0 w_1 w_2 \cdots$
over $\mathbb{Z}/2\mathbb{Z}$, its first difference is the infinite word $\Delta w$ over
$\mathbb{Z}/2\mathbb{Z}$ with $(\Delta w)_i = w_{i+1} - w_i$ for every natural number $i$. -/
def firstDifference (w : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  fun i ↦ w (i + 1) - w i

/-- **First difference of a finite binary word.** For a finite word $w = w_0 w_1 \cdots w_m$ over
$\mathbb{Z}/2\mathbb{Z}$, its first difference is the word
$(w_1 - w_0)(w_2 - w_1) \cdots (w_m - w_{m-1})$ of length $m$, computed in $\mathbb{Z}/2\mathbb{Z}$.
The first difference of the empty word is the empty word. -/
def firstDifferenceList (w : List (ZMod 2)) : List (ZMod 2) :=
  List.zipWith (· - ·) w.tail w

@[simp]
theorem length_firstDifferenceList (w : List (ZMod 2)) :
    (firstDifferenceList w).length = w.length - 1 := by
  cases w <;> simp [firstDifferenceList]

end MetaMathlibExt
