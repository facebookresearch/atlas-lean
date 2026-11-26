/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-!
# Tilings fixed by the second reflection of a rectangular grid

Transposing the grid turns the reflection $r^2 f$ into $f$. This gives the even-side count
from `rectangularGrid_f_even`, with the same permutation of tile designs.

## References

* Peter Kagey and William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1, pp. 13–14, Theorem 22, equations (4)
  and (5). <https://cs.uwaterloo.ca/journals/JIS/VOL27/Kagey/kagey6.html>
-/

namespace MetaMathlibExt

/-- **Cell map of the reflection r²f.** For natural numbers $n$ and $m$, the reflection $r^2 f$
acts on the pairs $(x, y) \in \mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}$ (for
$n, m \ge 1$, the cells of the $n \times m$ grid) by $(x, y) \mapsto (x, -1 - y)$, that is,
$(x, y) \mapsto (x, m - 1 - y)$ with the second coordinate taken modulo $m$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def cellR2F (n m : ℕ) (c : ZMod n × ZMod m) : ZMod n × ZMod m :=
  (c.1, -1 - c.2)

/-- **Rectangular-grid tilings fixed by the reflection $r^2 f$, $m$ even.** Let $n$ and $m$ be
positive integers with $m$ even, let $T$ be a finite set of tiles and let $\sigma$ be a
permutation of $T$ with $\sigma^2 = 1$. Let $g$ be the reflection $r^2 f$ of
$\mathbb{Z}/n \times \mathbb{Z}/m$, given by $g(x, y) = (x, -1 - y)$. Then the number of tilings
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(g(c)) = \sigma(F(c))$ for every cell $c$
equals $|T|^{nm/2}$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 22. -/
public theorem rectangularGrid_r2f_even {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1)
    (heven : Even m) :
    fixedTilingCount (cellR2F n m) σ = Fintype.card T ^ (n * m / 2) := by
  calc
    fixedTilingCount (cellR2F n m) σ = fixedTilingCount (cellF m n) σ := by
      unfold fixedTilingCount
      refine Fintype.card_congr ((Equiv.arrowCongr (Equiv.prodComm (ZMod n) (ZMod m))
        (Equiv.refl T)).subtypeEquiv ?_)
      -- Swapping the coordinates swaps which coordinate the reflection reverses.
      intro F
      constructor
      · rintro h ⟨y, x⟩
        exact h (x, y)
      · rintro h ⟨x, y⟩
        exact h (y, x)
    _ = Fintype.card T ^ (n * m / 2) := by
      simpa only [Nat.mul_comm m n] using rectangularGrid_f_even m n σ hσ heven

end MetaMathlibExt
