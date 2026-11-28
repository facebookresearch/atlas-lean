# Gross–Zagier–Kolyvagin, rank-one implication

Let $E/\mathbb{Q}$ be an elliptic curve,
and let $F$ be an entire function agreeing with the $L$-series of $E$ on the half-plane of
absolute convergence $\operatorname{Re}(s)>3/2$, so that $F$ is the entire continuation of the
Hasse–Weil $L$-function of $E$. If $F(1)=0$ and $F'(1)\ne 0$, that is, if this $L$-function has
a simple zero at $s=1$, then the Mordell–Weil rank of $E$ is one: the group $E(\mathbb{Q})$ of
rational points has rank one as a $\mathbb{Z}$-module.

This is the rank-one case of the rank equality in Robert L. Miller,
*Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank
zero and one*, LMS J. Comput. Math. 14 (2011), 327–350,
[Theorem 4.4, pp. 336–337](https://doi.org/10.1112/S1461157011000180).

## Informally uses

- [Modularity of elliptic curves over $\mathbb{Q}$](../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md), through which $E$ has a modular parametrization and $F$ exists
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](../zeta-l-functions/root-number-and-parity/functional-equation-of-the-l-function-of-an-elliptic-curve.md), for the root number $w(E) = -1$, forced by the simple zero of $F$ at $s = 1$
- [Quadratic twists with nonvanishing central value](../zeta-l-functions/nonvanishing-of-quadratic-twists-at-the-central-point.md), for a negative fundamental discriminant $D_K \ne -3, -4$, prime to the conductor, such that every prime factor of the conductor splits in $K = \mathbb{Q}(\sqrt{D_K})$ and $L(E, \varepsilon_K, 1) \ne 0$, so that $L(E/K, s) = L(E, s)\,L(E, \varepsilon_K, s)$ has a simple zero at $s = 1$
- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for a parametrization $\psi \colon X_0(N) \to E$, with $N$ the conductor of $E$, of minimal degree among those taking $\infty$ to $O$
- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-points-on-x0-n/heegner-point-of-an-elliptic-curve.md), for the point $y_K \in E(K)$ built with $\psi$
- [Gross–Zagier–Zhang formula: when the Heegner point has infinite order](gross-zagier-zhang-formula.md), by which $y_K$ has infinite order since $L'(E/K, 1) \ne 0$, whatever the parity of $D_K$
- [Kolyvagin's theorem on Heegner points](kolyvagin-descent/kolyvagin-s-theorem-on-heegner-points.md), by which $E(K)$ has rank $1$, so that $E(\mathbb{Q}) \subseteq E(K)$ has rank at most $1$
- [Complex conjugation on the Heegner point](complex-conjugation-and-the-trace/complex-conjugation-on-the-heegner-point.md), by which, as $w(E) = -1$, $y_K + \tau(y_K)$ is a point of infinite order in $E(\mathbb{Q})$, so that the rank is $1$
