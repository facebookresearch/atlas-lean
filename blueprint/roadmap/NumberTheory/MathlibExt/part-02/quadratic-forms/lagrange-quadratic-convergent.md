---
article_id: af_c3425d9e74ecbe296a7c6679
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lagrange_quadratic_convergent
---

# Lagrange Quadratic Convergent

A positive-denominator solution of `P u^2 + Q u y + R y^2 = 1` with negative
discriminant gives a convergent `u / y` of `ω = -Q / 2P`, outside the stated
exceptional discriminants. The conclusion uses Mathlib's canonical regular
continued fraction and `Real.convergent` API. The explicit validity condition
ensures that the selected index occurs before termination (with the initial
convergent handled separately), rather than relying on the totalized stable
tail of a terminating rational continued fraction.

The `D ≠ -3` exclusion and the `D = -4 → P ≠ 2` side condition are exactly
the source theorem's; a solution of `P*u^2+Q*u*y+R*y^2 = 1` automatically has
`gcd(u,y) = 1` as Lemma lemma:lagrange requires.

Proof: Following Matthews' Theorem `theorem:lagrange_lemma` and Lemma `lemma:lagrange`,
complete the square, establish the Legendre approximation bound, and choose its least convergent
index so that termination cannot have occurred earlier.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.QuadraticForms.LagrangeQuadraticConvergent](../../../../../sources/v2/MathlibExt.md)
- Keith R. Matthews, "Lagrange's Algorithm Revisited: Solving at^2 + btu + cu^2 = n in the Case of Negative Discriminant," Journal of Integer Sequences 17 (2014), Article 14.11.1, Theorem (label theorem:lagrange_lemma), lines 167–169, equation (label eq:01), lines 109–111, Lemma (label lemma:lagrange), lines 120–122, https://cs.uwaterloo.ca/journals/JIS/VOL17/Matthews/matt10.tex
