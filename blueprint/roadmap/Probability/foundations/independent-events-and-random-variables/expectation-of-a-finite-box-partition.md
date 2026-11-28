# Expectation of a simple function on a box partition

For a function that is constant on the boxes of a finite axis-aligned partition, its expectation is a finite sum: each box contributes its value times its probability, and under a product law that probability is a product of increments of one-dimensional distribution functions.

Let $\{\mathcal{T}_m\}_{m=1}^{M}$, $M \ge 1$, be disjoint axis-aligned boxes covering $\mathbb{R}^{D}$, each $\mathcal{T}_m = \prod_{d=1}^{D} (a_{m,d}, b_{m,d}]$ with $-\infty \le a_{m,d} < b_{m,d} \le +\infty$, and let $f$ take the constant value $f_m$ on $\mathcal{T}_m$. Let the random vector $\tilde{\boldsymbol{x}}_k$ have probability law $P_k$ on $\mathbb{R}^{D}$. Then

$$
\mathbb{E}\big[f(\tilde{\boldsymbol{x}}_k)\big] = \sum_{m=1}^{M} f_m \, P_k(\mathcal{T}_m) .
$$

If $P_k$ is a product of coordinate laws, with distribution functions $F_{k,d}$ extended by $F_{k,d}(-\infty) = 0$ and $F_{k,d}(+\infty) = 1$, then

$$
\mathbb{E}\big[f(\tilde{\boldsymbol{x}}_k)\big] = \sum_{m=1}^{M} f_m \prod_{d=1}^{D} \big[ F_{k,d}(b_{m,d}) - F_{k,d}(a_{m,d}) \big] .
$$

For $T \ge 1$ such surrogates, the $t$-th constant on its own finite partition $\{\mathcal{T}_{t,m}\}_{m=1}^{M_t}$ with values $f_{t,m}$, their average $\bar{f} = T^{-1}\sum_{t=1}^{T} f_t$ satisfies

$$
\mathbb{E}\big[\bar{f}(\tilde{\boldsymbol{x}}_k)\big] = \frac{1}{T} \sum_{t=1}^{T} \sum_{m=1}^{M_t} f_{t,m} \prod_{d=1}^{D} \big[ F_{k,d}(b_{t,m,d}) - F_{k,d}(a_{t,m,d}) \big] .
$$

The half-open boxes make the tile of a point unambiguous, and infinite endpoints are needed because a partition of $\mathbb{R}^{D}$ has unbounded tiles, for which no minimum or maximum coordinate exists; atomic coordinate laws are covered by the same displays. Integrability is automatic, since each surrogate takes finitely many values. The identities are exact for the surrogates, not for the objective they approximate: the error is the fitting error, not an integration error.

## Depends on

None. The finite partition and coordinate laws are stipulated in the statement.

## Proof depends on

- [Mass of a half-open interval via the cdf](../../distributions/distribution-functions/cumulative-distribution-function/measure-ioc-eq-of-real-cdf.md)

## Expansion

Split the integral over $\mathbb{R}^{D}$ into the tiles, pull the constant $f_m$ out of each piece, and recognize the remaining integral as $P_k(\mathcal{T}_m)$. For the second display, the product structure of $P_k$ gives $P_k(\mathcal{T}_m) = \prod_d P_{k,d}((a_{m,d}, b_{m,d}])$, and each factor is the increment of the coordinate distribution function, which the linked statement supplies for finite endpoints and monotone limits extend to infinite ones. The ensemble identity is linearity of expectation over the average of the $T$ surrogates.

An expansion should establish the finite-product rectangle rule for the stipulated product law, as well as the equivalent formulation using independent coordinate random variables. For the latter, Mathlib `ProbabilityTheory.iIndepFun.measure_inter_preimage_eq_mul` supplies the finite-product rule for preimages of measurable sets under an independent family. The factorized displays require this product-measure or independence bridge; the robust-counterpart definition alone does not supply it.

## Context

Graduate. The computational core of Golem by Aldeghi, Häse, Hickman, Tamblyn and Aspuru-Guzik: it turns an intractable integral into a closed-form sum, so robustness can be estimated at every candidate during a sequential laboratory campaign. No theory of regression trees is needed for a given finite partition.

## Sources

- Matteo Aldeghi, Florian Häse, Riley J. Hickman, Isaac Tamblyn and Alán Aspuru-Guzik, *Golem: an algorithm for robust experiment and process optimization*, Chemical Science 12 (2021) 14792–14807, supplementary Section S.1 A, Eqs. 13–20. DOI [10.1039/d1sc01545a](https://doi.org/10.1039/d1sc01545a), arXiv:[2103.03716v2](https://arxiv.org/abs/2103.03716v2).
