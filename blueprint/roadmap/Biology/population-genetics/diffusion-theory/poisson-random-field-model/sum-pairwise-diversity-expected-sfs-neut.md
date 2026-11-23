# Expected pairwise diversity of a neutral sample is θ

For every real $\theta$ and every natural number $n \ge 2$, the neutral ($\sigma = 0$)
[expected site frequency spectrum](expected-sfs.md) satisfies

$$\sum_{i=1}^{n-1} \frac{2i(n - i)}{n(n - 1)}\, \mathbb{E}\,\xi_i = \theta.$$

The weight $2i(n - i)/(n(n - 1))$ is the probability that two distinct gene copies drawn from the
sample differ at a site where $i$ of the $n$ copies carry the derived allele, so for
$\theta \ge 0$ the sum is the expected pairwise diversity of the sample.
