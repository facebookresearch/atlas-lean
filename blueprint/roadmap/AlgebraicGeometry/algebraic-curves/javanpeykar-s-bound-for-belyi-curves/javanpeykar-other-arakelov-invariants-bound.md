# Javanpeykar's bounds for the other Arakelov invariants of a Belyi curve

This node is still to be broken down. Let $X$ be a smooth projective connected curve over
$\overline{\mathbb{Q}}$ of genus $g \ge 1$, with [Belyi degree](belyi-degree.md) $\deg_B(X)$ and
[Arakelov invariants](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md) $e(X)$, $\Delta(X)$ and
$\delta_{\mathrm{Fal}}(X)$. Then

$$0 \le e(X) \le 3 \cdot 10^7 (g - 1) \deg_B(X)^5,$$

$$0 \le \Delta(X) \le 5 \cdot 10^8 g^2 \deg_B(X)^5,$$

$$-10^8 g^2 \deg_B(X)^5 \le \delta_{\mathrm{Fal}}(X) \le 2 \cdot 10^8 g \deg_B(X)^5.$$

These are the bounds of Javanpeykar's Theorem 1.1.1 other than the one for the Faltings height,
which is [Javanpeykar's bound for the Faltings height of a Belyi curve](javanpeykar-faltings-height-bound.md).

## Depends on

- [Belyi degree](belyi-degree.md)
- [Arakelov invariants of a curve over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md)

## Proof depends on

- [Belyi's theorem](belyi-s-theorem.md), so that $\deg_B(X)$ is the degree of a Belyi map
- [Faltings' bounds for the self-intersection of the dualizing sheaf](../arakelov-invariants-of-curves/faltings-self-intersection-bounds.md), for $e(X) \ge 0$
- [A non-Weierstrass point of bounded height on a Belyi curve](non-weierstrass-point-of-bounded-height.md)
- [Bound for the Wronskian differential of a Belyi cover](wronskian-bound-for-belyi-covers.md)
- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md), to view a Belyi map as a Belyi
  cover of $X(2)$
- [Arakelov invariants bounded by the height of a non-Weierstrass point](arakelov-invariants-and-a-non-weierstrass-point.md)

The other inputs are listed under Expansion.

## Expansion

The proof (§4.6) takes a non-Weierstrass point $b$ with $h(b) \le 6378033 \deg_B(X)^5 / g$ and
$\log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b) \le 6378028 \, g \deg_B(X)^5$ and substitutes them
into the bounds by the height of a non-Weierstrass point; $\Delta(X) \ge 0$ is immediate. A good
expansion has a page for the effective constants, which use $g \le \deg_B(X)$ (Lemma 3.2.2,
p. 106) to absorb the terms in $g^3$, for instance $e(X) \le 4(g - 1) \cdot 6378033 \deg_B(X)^5$.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Theorem 1.1.1, p. 90, and its proof in §4.6, p. 123.
