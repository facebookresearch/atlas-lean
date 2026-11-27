# Arakelov invariants bounded by the height of a non-Weierstrass point

This node is still to be broken down. Let $X$ be a smooth projective connected curve over
$\overline{\mathbb{Q}}$ of genus $g \ge 1$, with
[Arakelov invariants](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md) $e(X)$, $\Delta(X)$ and
$\delta_{\mathrm{Fal}}(X)$, Faltings height $h_{\mathrm{Fal}}(X)$, height function $h$ and Arakelov
norm of the Wronskian differential $\lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}$. Let $b \in
X(\overline{\mathbb{Q}})$. Then

$$e(X) \le 4g(g - 1) \, h(b), \qquad \delta_{\mathrm{Fal}}(X) \ge -90 g^3 - 4g(2g - 1)(g + 1) \,
h(b).$$

If $b$ is not a Weierstrass point, then

$$h_{\mathrm{Fal}}(X) \le \tfrac12 g(g + 1) \, h(b) + \log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b),$$

$$\delta_{\mathrm{Fal}}(X) \le 6g(g + 1) \, h(b) + 12 \log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b) +
4g \log(2\pi),$$

$$\Delta(X) \le 2g(g + 1)(4g + 1) \, h(b) + 12 \log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b) + 93
g^3.$$

## Depends on

- [Arakelov invariants of a curve over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md)

## Proof depends on

- [Faltings' bounds for the self-intersection of the dualizing sheaf](../arakelov-invariants-of-curves/faltings-self-intersection-bounds.md)
- [Noether's formula for curves over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/noether-formula.md)
- [Bost's lower bound for the Faltings height](../../abelian-varieties/stable-faltings-height/bost-lower-bound.md),
  applied to the Jacobian: $h_{\mathrm{Fal}}(X) \ge -\frac{g}{2} \log(2\pi^2) \ge -g \log(2\pi)$
  (Lemma 2.4.4)
- [The Jacobian has dimension equal to the genus](../jacobians-of-curves/smooth-of-relative-dimension-genus.md),
  so that Bost's bound applies with dimension $g$

The other inputs are listed under Expansion.

## Expansion

The bound for $h_{\mathrm{Fal}}$ is de Jong's Theorem 5.9 combined with
$\mathrm{gr}_X(\mathcal{W}, b) - \log R(X) = \log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b)$
(eq. (4), p. 95); the upper bounds for $\delta_{\mathrm{Fal}}$ and $\Delta$ follow from it, from
Noether's formula and from $e(X), \Delta(X) \ge 0$. The lower bound for $\delta_{\mathrm{Fal}}$
uses, for $g \ge 2$, Proposition 2.4.8 with Lemmas 2.4.2–2.4.6 (pp. 100–103), and for $g = 1$ a
result of Szpiro. A good expansion has pages for: de Jong 2005a, Theorem 5.9 and Proposition 5.6,
and the invariants $S(X)$ and $R(X)$ with eqs. (2)–(4) (p. 95); Lemma 2.4.2, the bound for $\log
\lVert \vartheta \rVert_{\max}(X)$ from Bost's bound on $\det \Im(\tau_\sigma)$ (Graftieaux 2001,
Lemme 2.12, as cited on p. 100); Lemma 2.4.3; Proposition 2.4.8; and Szpiro's bound for $g = 1$
(de Jong 2005b, Proposition 7.2, as cited on p. 103). The sources cited only through Javanpeykar
were not read here.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Theorem 2.4.1, pp. 99–100, with Lemmas 2.4.2–2.4.7 and Proposition 2.4.8 and the
  proof of Theorem 2.4.1, pp. 100–104. Lemma 2.4.4 (Bost) is É. Gaudron and G. Rémond, Corollaire
  8.4, in Javanpeykar's normalization, p. 101.
