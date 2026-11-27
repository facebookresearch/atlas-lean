# Subsampling theorem for f-differential privacy

Let $f$ be a symmetric trade-off function, let $M$ be $f$-DP and let $M \circ \mathrm{Sample}_m$ run $M$ on a uniformly random subset of $m$ of the $n$ records (sampling without replacement), with sampling ratio $p = m/n$ and neighbouring datasets differing by replacement of one record. Write $f_p = p f + (1-p)\,\mathrm{Id}$ with $\mathrm{Id}(\alpha) = 1 - \alpha$. Then $M \circ \mathrm{Sample}_m$ is

$$
\min\{f_p, f_p^{-1}\}^{**}\text{-DP},
$$

where $g^{**}$ is the double convex conjugate (the largest convex function below $g$), and this bound improves the corresponding subsampling bounds for $(\varepsilon,\delta)$-DP obtained through the primal–dual conversion.

## Proof sketch

The tempting direct argument, that each neighbouring pair of subsampled outputs is a mixture of an identical pair and an $f$-DP pair and therefore has trade-off function at least $f_p$ in one direction and $f_p^{-1}$ in the other, is false in general: with $m = 1$, $n = 2$ and binary randomized response that is truthful with probability $3/4$, testing the subsampled output on the dataset $(0,1)$ against $(0,0)$ at type I error $1/2$ achieves type II error $1/4$, below $f_p(1/2) = 1/3$. The proof instead goes through approximate differential privacy. By the primal–dual conversion, $M$ is $(\varepsilon, 1 + f^*(-e^{\varepsilon}))$-DP for every $\varepsilon \ge 0$. Amplification by subsampling without replacement turns each of these into an $(\varepsilon', \delta')$ guarantee with $\varepsilon' = \log(1 - p + p e^{\varepsilon})$ and $\delta' = p(1 + f^*(-e^{\varepsilon}))$; eliminating $\varepsilon$ gives $\delta' = 1 + f_p^*(-e^{\varepsilon'})$. Since $f_p$ is not symmetric, a version of the primal–dual conversion for general trade-off functions shows that this family of guarantees for all $\varepsilon' \ge 0$ is equivalent to $\min\{f_p, f_p^{-1}\}^{**}$-DP, the lower convex envelope of the minimum.

## Depends on

- [f-differential privacy](f-differential-privacy.md)

## Proof depends on

- [Primal–dual conversion between f-DP and families of approximate DP guarantees](f-dp-primal-dual-conversion.md)
- [Tight privacy amplification by subsampling](../shuffle-model-and-privacy-amplification/privacy-amplification-by-subsampling.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Theorem 4.2, Section 4.2 and Proposition 4.5.
