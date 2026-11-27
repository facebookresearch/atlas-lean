/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-!
# Reflection-fixed tilings of an even square grid

The rectangular reflection formula specializes to the square by taking equal side lengths.
-/

namespace MetaMathlibExt

/-- **Square-grid tilings fixed by the reflection $f$ for even $n$.** Let $n$ be an even positive
integer, let $T$ be a finite set and let $\sigma$ be a permutation of $T$ with $\sigma^2 = 1$.
Let $f$ be the reflection of the grid $(\mathbb{Z}/n\mathbb{Z})^2$ given by
$f(x, y) = (-1 - x, y)$. Then the number of maps $F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with
$F(f(c)) = \sigma(F(c))$ for every cell $c$ is $|T|^{n^2/2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_f_even {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) (heven : Even n) :
    fixedTilingCount (cellF n n) σ = Fintype.card T ^ (n ^ 2 / 2) := by
  simpa only [sq] using rectangularGrid_f_even n n σ hσ heven

end MetaMathlibExt
