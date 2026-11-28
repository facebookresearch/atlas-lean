/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridSecondReflectionTilings

/-!
# Tilings fixed by the second reflection of an even square grid

The even square-grid count is the rectangular-grid count with both sides equal.

## References

* Peter Kagey and William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1, p. 15, Theorem 24, equation (10),
  specializing Theorem 22, equation (5).
  <https://cs.uwaterloo.ca/journals/JIS/VOL27/Kagey/kagey6.html>
-/

namespace MetaMathlibExt

/-- **Square-grid tilings fixed by the reflection $r^2 f$ for even $n$.** Let $n$ be an even
positive integer, let $T$ be a finite set and let $\sigma$ be a permutation of $T$ with
$\sigma^2 = 1$. Let $r^2 f$ be the reflection of the grid $(\mathbb{Z}/n\mathbb{Z})^2$ given by
$(r^2 f)(x, y) = (x, -1 - y)$. Then the number of maps $F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$
with $F((r^2 f)(c)) = \sigma(F(c))$ for every cell $c$ is $|T|^{n^2/2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 24. -/
public theorem squareGrid_r2f_even {T : Type*} [Fintype T] [DecidableEq T]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) (heven : Even n) :
    fixedTilingCount (cellR2F n n) σ = Fintype.card T ^ (n ^ 2 / 2) := by
  simpa only [pow_two] using rectangularGrid_r2f_even n n σ hσ heven

end MetaMathlibExt
