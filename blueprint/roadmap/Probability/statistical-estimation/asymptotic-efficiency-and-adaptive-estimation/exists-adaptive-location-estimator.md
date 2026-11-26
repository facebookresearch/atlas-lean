# Adaptive estimation of a centre of symmetry

Consider i.i.d. observations $X_i = \theta + \varepsilon_i$, where the law $G$ of $\varepsilon_i$ is unknown apart from being symmetric about $0$: a semiparametric model with Euclidean parameter $\theta$ and infinite-dimensional nuisance parameter $G$. For a law $G$ with density $g$, its Fisher information for location is

$$I(G) = \int \frac{g'(x)^2}{g(x)} \, dx$$

when $g$ is absolutely continuous (and $I(G) = \infty$ otherwise).

There are measurable estimators $T_n(X_1, \dots, X_n)$, $n \ge 1$, equivariant under translations ($T_n(x + c) = T_n(x) + c$) and under positive rescalings ($T_n(a x) = a T_n(x)$ for $a > 0$), such that for every symmetric $G$ with an absolutely continuous density and $I(G) < \infty$,

$$\sqrt n \, T_n(X_1, \dots, X_n) \xrightarrow{d} N\bigl(0, I(G)^{-1}\bigr) \quad\text{for } X_i \text{ i.i.d. } G .$$

By translation equivariance the same holds at every $\theta$ for $\sqrt n(T_n - \theta)$. Since $I(G)^{-1}$ is the information bound of the parametric model in which $G$ is known, the estimators are *adaptive*: not knowing $G$ costs nothing asymptotically. Bickel (1982) derives sufficient conditions for adaptation, motivated by Stein's (1956) necessary condition, and applies them to the parameters of linear models and of multivariate elliptic distributions.

The estimators are indexed by all $n \in \mathbb N$, but equivariance is required only for samples of size $n \ge 1$: on the empty sample translation equivariance would force $T_0 = T_0 + c$, which no map satisfies. Weak convergence is tested against bounded continuous functions, and the limit variance is written $(\int g'^2/g)^{-1}$; the integral is positive for every probability density covered by the hypotheses.

## Background

- [Hájek's convolution theorem](hajek-convolution.md): the bound $I(G)^{-1}$ for regular estimators in the model with $G$ known.
- [Fisher information](../fisher-information-and-the-cram-r-rao-bound/fisher-information.md): the information of a one-parameter density family, here the location family of $g$.

## Sources

- P. J. Bickel, "On adaptive estimation", *Ann. Statist.* 10 (1982) 647–671, Example 1 and Theorem 2.2, which Bickel attributes to R. Beran (1974) and C. J. Stone (1975).
