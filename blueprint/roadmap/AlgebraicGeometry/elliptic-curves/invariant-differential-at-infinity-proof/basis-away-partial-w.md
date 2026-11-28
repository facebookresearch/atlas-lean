# `Ω¹_S` is free with basis `dz`

Let `W` be a Weierstrass curve over a commutative ring `R`
and let `S = B_W[1 / h_w]` be the part of the chart at infinity `B_W = R[z, w] / (h)` where
`h_w = ∂h/∂w` is invertible; it contains the point at infinity `z = w = 0`, where `h_w = 1`. Then
`Ω¹_{S/R}` is a free `S`-module with the one-element basis `dz` (`basisAwayPartialW_apply`).

The source works over a field and with `Δ_W ≠ 0`; neither hypothesis is used: `R` is any
commutative ring and `W` any Weierstrass curve. This is the algebraic input to Milne's remark
that the invariant differential is holomorphic at the point at infinity.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §6, p. 211 ("One can check that it also holomorphic at the point at infinity"); the Stacks project, Lemma 10.131.8, <https://stacks.math.columbia.edu/tag/00RT>.
