# A non-Weierstrass point of bounded height on a Belyi curve

This node is still to be broken down. Let $Y$ be a smooth projective connected curve over
$\overline{\mathbb{Q}}$ of genus $g \ge 1$. For every finite morphism $\pi \colon Y \to
\mathbb{P}^1_{\overline{\mathbb{Q}}}$ ramified over exactly three points there is a
non-Weierstrass point $b$ of $Y$ whose
[height](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md) satisfies

$$h(b) \le 6378033 \, \frac{(\deg \pi)^5}{g}.$$

## Depends on

- [Arakelov invariants of a curve over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md), for the
  height and the Weierstrass points

## Proof depends on

- [Height bound for points of a Belyi curve above small rational numbers](height-bound-above-small-rationals.md)

The other inputs are listed under Expansion.

## Expansion

After an automorphism of $\mathbb{P}^1$, $\pi$ is unramified over $\mathbb{P}^1 \setminus \{0, 1,
\infty\}$. With $a_1 = \frac12$ and $a_n = n/(2n - 1)$ for $n \ge 2$, one has $\frac12 \le a_n \le
\frac23$ and $h_{\mathrm{naive}}(a_n) \le \log(2n)$; since $Y$ has at most $g^3 - g$ Weierstrass
points, some fibre $\pi^{-1}(a_i)$ with $1 \le i \le (\deg \pi)^2$ contains a non-Weierstrass
point, and $3 \log(2 (\deg \pi)^2) (\deg \pi)^2 \le 2 (\deg \pi)^5 / g$. A good expansion has pages
for the Möbius normalization of the three branch points and for the bound $g^3 - g$ on the number
of Weierstrass points, from the degree of the divisor of the Wronskian differential (p. 95).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Theorem 4.5.2 and its proof, pp. 122–123.
