# Representation by ternary quadratic forms over $\mathbb{Q}_p$ and $\mathbb{R}$

Let $K$ be the field $\mathbb{R}$ or the field $\mathbb{Q}_p$ for a prime $p$ ($p = 2$ included).
Let $f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ with $a_1, a_2, a_3 \in K^\times$, and let
$d = a_1 a_2 a_3$. Call $f$ isotropic over $K$ if $f(x) = 0$ for some nonzero $x \in K^3$.

1. $f$ is isotropic over $K$ if and only if the Hilbert symbol $(-a_1 a_2, -a_1 a_3)_K$ equals $1$.
2. For $a \in K^\times$, the equation $f(x) = a$ has a solution $x \in K^3$ if and only if $f$ is
   isotropic over $K$ or $-ad$ is not a square in $K$.

Here $(b, c)_K$ is the Hilbert symbol of $K$: $1$ if $b x^2 + c y^2 = 1$ has a solution in $K$, and
$-1$ otherwise. For nonzero $b, c$ this is $1$ exactly when $z^2 - b x^2 - c y^2$ has a nonzero
zero: a solution of $b x^2 + c y^2 = 1$ gives the zero $(x, y, 1)$, and a nonzero zero with $z = 0$
makes $b x^2 + c y^2$ a hyperbolic plane, which takes every value, $1$ included.

This node is still to be broken down. Part 1 follows from that description of the symbol applied to
$a_1^{-1} f$, as $-a_2/a_1$ and $-a_1 a_2$ differ by a square. Part 2 is the ternary case of the
criterion for a form over $K$ to represent an element in terms of its rank, its discriminant $d$ and
its invariant $\varepsilon = \prod_{i<j} (a_i, a_j)$: an isotropic nondegenerate form represents every
element, and an anisotropic ternary form represents exactly the classes in
$K^\times / K^{\times 2}$ other than that of $-d$.

## Expansion

A good expansion states and links:

- the bilinearity and nondegeneracy of the Hilbert symbol on $K^\times / K^{\times 2}$, which follow
  from its formula (Serre, Chapter III, §1);
- the passage between representing $a$ by $f$ and representing $0$ by $f - a\,x_4^2$, and the fact
  that an isotropic nondegenerate form represents every element (Serre, Chapter IV, §1.6);
- the invariants $d$ and $\varepsilon$ (Serre, Chapter IV, §2.1) and the criteria for a form over
  $\mathbb{Q}_p$ of rank $3$ and $4$ to represent $0$, from which part 2 follows for
  $K = \mathbb{Q}_p$ (Serre, Chapter IV, §2);
- the real case, by signature (Serre, Chapter IV, §2.4).

## Depends on

- [The $p$-adic Hilbert symbol](../p-adic-numbers/hilbert-symbol/padic-hilbert-symbol.md), for $(b, c)_K$ when $K = \mathbb{Q}_p$
- [Real Hilbert symbol](../p-adic-numbers/hilbert-symbol/real-hilbert-symbol.md), for $(b, c)_K$ when $K = \mathbb{R}$

## Proof depends on

- [Formula for the $p$-adic Hilbert symbol at an odd prime](../p-adic-numbers/hilbert-symbol/padic-hilbert-symbol-formula.md) and [Formula for the $2$-adic Hilbert symbol](../p-adic-numbers/hilbert-symbol/dyadic-hilbert-symbol-formula.md), for the values of the symbol on $\mathbb{Q}_p^\times / \mathbb{Q}_p^{\times 2}$ for odd $p$ and for $p = 2$, from which its bilinearity and nondegeneracy follow
- [Sign rule for the real Hilbert symbol](../p-adic-numbers/hilbert-symbol/eq-neg-one-iff-both-neg.md), for the real case

The rest of its proof is that of the source below, as the Expansion describes.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1 (local properties of the Hilbert symbol; its definition in §1.1), pp. 19–23; Chapter IV, §1.6
  (represented elements), in §1, pp. 27–35; Chapter IV, §2 (quadratic forms over $\mathbb{Q}_p$:
  the invariants $d$ and $\varepsilon$ in §2.1, the real case in §2.4), pp. 35–41, the case $n = 3$.
