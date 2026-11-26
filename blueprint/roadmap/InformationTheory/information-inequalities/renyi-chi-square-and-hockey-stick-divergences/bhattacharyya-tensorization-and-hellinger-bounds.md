# Tensorization of the Bhattacharyya coefficient and Hellinger bounds on product distances

For distributions $p, q$ on a finite set let $\mathrm{BC}$, $h^2 = 1 - \mathrm{BC}$, $h = \sqrt{h^2}$ and $\delta$ be as in the divergence comparison hierarchy. Then:

1. $\mathrm{BC}(\bigotimes_i p_i, \bigotimes_i q_i) = \prod_i \mathrm{BC}(p_i, q_i)$; hence $h^2(\bigotimes_i p_i, \bigotimes_i q_i) \le \sum_i h^2(p_i, q_i)$ and $h(p^{\otimes n}, q^{\otimes n}) \le \sqrt{n}\, h(p,q)$.
2. $h^2(p,q) \le \delta(p,q) \le h(p,q)\sqrt{2 - h^2(p,q)} \le \sqrt2\, h(p,q)$.
3. Consequently $\delta(p^{\otimes n}, q^{\otimes n}) \le \sqrt{2n}\, h(p,q)$ and $\delta(\bigotimes_i p_i, \bigotimes_i q_i) \le \sqrt{2\sum_i h^2(p_i, q_i)}$.
4. $h$ is a metric, $\mathrm{BC}$ is jointly concave, and $h^2(pK, qK) \le h^2(p, q)$ for every Markov kernel $K$.

## Proof sketch

The product formula is immediate since square roots of products factor; then $1 - \prod_i(1 - a_i) \le \sum_i a_i$. For item 2, $\sum_x\min(p,q) \le \mathrm{BC}$ gives the lower bound, and Cauchy-Schwarz on $|p - q| = |\sqrt p - \sqrt q|(\sqrt p + \sqrt q)$ gives Le Cam's upper bound. Item 3 combines 1 and 2; item 4 follows from concavity of $(u,v) \mapsto \sqrt{uv}$.

## Depends on

- [Hellinger distance](../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)
- [Total variation is at most √2 times Hellinger](../../../Probability/convergence-of-measures/hellinger-distance/total-variation-dist-div-sqrt-two-le-hel.md)

## Proof depends on

- [Hellinger is at most the square root of total variation](../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist-le-sqrt-total-variation-d.md)

## Sources

- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- C. L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
