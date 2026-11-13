/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Finite overlap-free binary words

Source: J. D. Currie, *The analog of overlap-freeness for the period-doubling sequence*,
Journal of Integer Sequences 26 (2023),
[`currie16.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL26/Currie/currie16.tex).
-/

/-- **Overlaps in words.** A finite word $o$ over an alphabet $\alpha$ is an overlap if
$o = xyxyx$ for some finite words $x$ and $y$ over $\alpha$ with $x$ nonempty; $y$ may be empty.

Here $x$ may have any positive length, not only length one. -/
public def IsWordOverlap {α : Type*} (o : List α) : Prop :=
  ∃ x y : List α, x ≠ [] ∧ o = x ++ y ++ x ++ y ++ x

/-- A finite binary word is overlap-free when none of its contiguous factors is an overlap. -/
public def IsOverlapFreeBinaryWord (w : List Bool) : Prop :=
  ∀ o : List Bool, o.IsInfix w → ¬ IsWordOverlap o

end

end MetaMathlibExt
