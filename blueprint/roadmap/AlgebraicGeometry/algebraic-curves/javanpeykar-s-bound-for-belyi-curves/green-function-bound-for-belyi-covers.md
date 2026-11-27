# Bound for the Arakelov–Green function of a Belyi cover

This node is still to be broken down. Let $\pi \colon Y \to X(2)$ be a
[Belyi cover](belyi-cover-of-x2.md) such that $Y$ has genus $g \ge 1$, with
[Arakelov–Green function](../arakelov-invariants-of-curves/arakelov-green-function.md) $\mathrm{gr}_Y$. Then

$$\sup_{(Y \times Y) \setminus \Delta} \mathrm{gr}_Y \le 6378027 \, \frac{(\deg \pi)^5}{g}.$$

Moreover, for every cusp $y$ and all $x \ne x'$ in $V_y^{r_1}$,

$$\bigl\lvert \mathrm{gr}_Y(x, x') - \log \lvert w_y(x) - w_y(x') \rvert \bigr\rvert \le 6378027 \,
\frac{(\deg \pi)^5}{g}.$$

## Depends on

- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md)
- [Arakelov $(1,1)$-form and Arakelov–Green function](../arakelov-invariants-of-curves/arakelov-green-function.md)

## Proof depends on

- [Merkl's bound for the Arakelov–Green function](../arakelov-invariants-of-curves/merkl-s-theorem.md)
- [Bound for the Arakelov form in the cusp charts of a Belyi cover](arakelov-form-in-cusp-charts.md)

The other inputs are listed under Expansion.

## Expansion

The proof checks that the cusp charts, with $r_1$, $M = 4d \exp(3\pi)$ and $c_1 = 128 \exp(3\pi)
d^4 / (\pi^2 g)$ for $d = \deg \pi$, form a Merkl atlas. A good expansion has pages for: Lemma
3.4.1, $\lvert dz_\kappa / dz_{\kappa'} \rvert \le 4 \exp(3\pi/2)$ on $B_\kappa \cap B_{\kappa'}$
(p. 108); the covering of $Y$ by the $V_y^{r_1}$, from $X(2) = \bigcup_\kappa B_\kappa^{s_1}$; the
bound $n \le 3d$ on the number of cusps and $1/(1 - r_1) \le d / (1 - s_1)$; and the numerical
inequality that bounds Merkl's constant by $6378027 \, d^5 / g$ (pp. 110–111).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Theorem 3.4.5 and its proof, pp. 110–111, with Lemma 3.4.1, p. 108.
