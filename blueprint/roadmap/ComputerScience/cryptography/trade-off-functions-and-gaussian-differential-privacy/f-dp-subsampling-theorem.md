# Subsampling theorem for f-differential privacy

Let $M$ be $f$-DP and let $M \circ \mathrm{Sample}_m$ run $M$ on a uniformly random subset of $m$ of the $n$ records (sampling without replacement), with sampling ratio $p = m/n$ and neighbouring datasets differing by replacement of one record. Write $f_p = p f + (1-p)\,\mathrm{Id}$ with $\mathrm{Id}(\alpha) = 1 - \alpha$. Then $M \circ \mathrm{Sample}_m$ is

$$
\min\{f_p, f_p^{-1}\}^{**}\text{-DP},
$$

where $g^{**}$ is the double convex conjugate (the largest convex function below $g$), and this bound improves the corresponding subsampling bounds for $(\varepsilon,\delta)$-DP obtained through the primal–dual conversion.

## Proof sketch

With probability $1-p$ the differing record is not sampled and the two output distributions coincide; with probability $p$ it is, and the outputs are a neighbouring pair for $M$. Hence each neighbouring pair of outputs is a mixture of an identical pair and an $f$-DP pair with the same weights, whose trade-off function is at least $f_p$ in one direction and $f_p^{-1}$ in the other; the symmetric hull and convexification follow from the closure properties of trade-off functions.

## Depends on

- [f-differential privacy](f-differential-privacy.md)

## Proof depends on

- [Primal–dual conversion between f-DP and families of approximate DP guarantees](f-dp-primal-dual-conversion.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
