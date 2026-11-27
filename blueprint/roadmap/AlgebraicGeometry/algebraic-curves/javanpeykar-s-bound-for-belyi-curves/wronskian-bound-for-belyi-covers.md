# Bound for the Wronskian differential of a Belyi cover

This node is still to be broken down. Let $\pi \colon Y \to X(2)$ be a
[Belyi cover](belyi-cover-of-x2.md) with $Y$ of genus $g \ge 1$, and let $\lVert \mathrm{Wr}
\rVert_{\mathrm{Ar}}$ be the Arakelov norm of the
[Wronskian differential](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md) of $Y$, with divisor of
Weierstrass points $\mathcal{W}$. Then

$$\sup_{Y \setminus \operatorname{Supp} \mathcal{W}} \log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}
\le 6378028 \, g (\deg \pi)^5.$$

## Depends on

- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md)
- [Arakelov invariants of a curve over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md), for the
  Wronskian differential and its Arakelov norm

## Proof depends on

- [Bound for the Arakelov–Green function of a Belyi cover](green-function-bound-for-belyi-covers.md)
- [Bound for the Arakelov form in the cusp charts of a Belyi cover](arakelov-form-in-cusp-charts.md)

The other inputs are listed under Expansion.

## Expansion

For a non-Weierstrass point $b \in V_y^{r_1}$, $\log \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b) =
\log \lvert W_{w_y}(\omega)(b) \rvert + \frac{g(g+1)}{2} \log \lVert dw_y \rVert_{\mathrm{Ar}}(b)$;
the second term is at most $6378027 \, g (\deg \pi)^5$ by the Green function bound, and the first
at most $13 g (\deg \pi)^2 \le g (\deg \pi)^5$, as $\deg \pi \ge 3$. A good expansion has pages for
that formula, Hadamard's inequality, Cauchy's integral formula for the derivatives of the $f_k$,
$\sum_k \lvert f_k \rvert^2 = 2g F_y$, and the bound $\deg \pi \ge 3$ when $g \ge 1$ (pp. 111–112).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Proposition 3.5.1 and its proof, pp. 111–112.
