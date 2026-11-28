# Singular points of Weierstrass cubics

Let `F` be a field with algebraic closure `F̄`
(more generally, let `K` be any algebraically closed field containing `F`), and let
`C ⊂ ℙ²` be the plane cubic
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`, `a₁, …, a₆ ∈ F`, with the quantities `c₄`
and `Δ` of `W`. Then

1. `C` is nonsingular over `K` if and only if `Δ ≠ 0`;
2. if `Δ = 0`, then `C_K` has exactly one singular point `S` (up to scaling), and
   `S ≠ (0 : 1 : 0)`; it is a node if `c₄ ≠ 0` and a cusp if `c₄ = 0`.

A singular point is a node if it is a double point with two distinct tangent lines
(`WeierstrassCurve.IsNode`), and a cusp if it is a double point with a single tangent line `L`
and the intersection number of `L` and the curve at the point is `3`
(`WeierstrassCurve.IsCusp`, with the intersection number of a line computed by restriction,
`WeierstrassCurve.lineIntersectionNumber`).

## Sources

- J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, author's version <https://www.jmilne.org/math/Books/EC2.pdf>: Chapter I, §1, p. 8 (multiplicity, tangent lines, nodes) and Remark 1.12, p. 11 (cusps); Chapter II, Theorem 2.4(a), p. 52 (the curve is nonsingular if and only if `Δ ≠ 0`); Chapter II, §3, pp. 57–59 (p. 58: "the point `(0 : 1 : 0)` is always nonsingular"; p. 59: "the singularity is cusp if `c4 = 0` and a node if `c4 ≠ 0`", citing J. Tate, Invent. Math. 23 (1974), p. 182).
