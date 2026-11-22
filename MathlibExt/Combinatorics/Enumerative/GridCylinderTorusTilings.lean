/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Tilings of grids, cylinders, and tori: the reflection-shift equation for odd moduli

On the `n × m` cylinder, applying the shift `x ↦ x + a` and then the reflection
`x ↦ n - 1 - x` sends the column `x` to `-1 - x - a` modulo `n`, so the columns this map fixes
are the solutions of `x = -1 - x - a` in `ZMod n`. Kagey and Keehn solve this equation according
to the parities of `n` and `a`; this file proves the case of an odd modulus.

## Main results

* `MetaMathlibExt.reflection_shift_solutions_odd`: for odd `n`, the solutions of
  `x = -1 - x - a` in `ZMod n` form the singleton `{((n + 1) / 2) * (-1 - a)}`.

## Implementation notes

The equation says `2 * x = -1 - a`. For odd `n` the division `(n + 1) / 2` is exact, and the
residue of its quotient is the inverse of `2` in `ZMod n`, since `2 * ((n + 1) / 2) = n + 1`.
Multiplying by it solves the equation, and multiplying back by `2` shows the solution is unique.

## References

* Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1; arXiv:2311.13072v2, Lemma 3.0.1.
-/

namespace MetaMathlibExt

/-- **Solution of $x = -1-x-a$ modulo odd $n$.** Let $n$ be a positive odd integer and
$a \in \mathbb{Z}/n$. Then the set of $x \in \mathbb{Z}/n$ with $x = -1-x-a$ is the singleton
$\{k(-1-a)\}$, where $k$ is the residue mod $n$ of the integer $(n+1)/2$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_odd (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Odd n) :
    {x : ZMod n | x = -1 - x - a} =
      {(((n + 1) / 2 : ℕ) : ZMod n) * (-1 - a)} := by
  -- The residue of `(n + 1) / 2` is the inverse of `2`: twice it is `n + 1 = 1` in `ZMod n`.
  have hinv : (((n + 1) / 2 : ℕ) : ZMod n) * 2 = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod n)
      (Nat.div_mul_cancel (even_iff_two_dvd.mp hn.add_one))
    push_cast at h
    simpa using h
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    linear_combination (((n + 1) / 2 : ℕ) : ZMod n) * hx - x * hinv
  · rintro rfl
    linear_combination (-1 - a) * hinv

end MetaMathlibExt
