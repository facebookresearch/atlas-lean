# Raz's conditioning lemma for product distributions

Let $U = (U_1, \dots, U_k)$ have independent coordinates, $U_j \sim p_j$ on finite sets, so $U \sim \bigotimes_j p_j$, and let $W$ be an event with $\Pr[W] > 0$. Write $P_{U_j \mid W}$ for the law of $U_j$ conditioned on $W$. Then, with $\delta$ the statistical distance and $\ln$ the natural logarithm,

$$
\sum_{j=1}^{k} \delta\big(P_{U_j \mid W}, p_j\big)^2 \le \frac12 \ln\frac{1}{\Pr[W]},
$$

hence $\Pr[W] \le 2^{-\sum_j \delta(P_{U_j\mid W}, p_j)^2}$, and for every set $J$ of $m$ coordinates $\sum_{j \in J}\delta(P_{U_j\mid W}, p_j) \le \sqrt{m \ln(1/\Pr[W])/2}$. More generally, for any distribution $P$ on the product, $\sum_j D(P_j\|p_j) \le D(P\|\bigotimes_j p_j)$ where $P_j$ are the marginals of $P$ (superadditivity of divergence from a product).

## Proof sketch

Conditioning on $W$ produces the distribution $P = P_{U\mid W}$ with $D(P\|\bigotimes_j p_j) = \ln(1/\Pr[W])$ exactly. The gap $D(P\|\bigotimes_j p_j) - \sum_j D(P_j\|p_j)$ equals the divergence of $P$ from the product of its own marginals, which is nonnegative by Gibbs' inequality. Pinsker's inequality for each marginal and Cauchy-Schwarz over $J$ complete the proof.

## Depends on

- [Kullback–Leibler divergence of finite probability laws](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md)

## Proof depends on

- [Tensorization of KL divergence and product Pinsker bounds](kl-tensorization-for-products.md)
- [Gibbs' inequality](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)
- [Csiszár–Kullback–Pinsker inequality with zero entries allowed](../csiszar-kullback-pinsker-of-nonneg.md)

## Sources

- R. Raz, "A Parallel Repetition Theorem", SIAM Journal on Computing 27(3), 1998.
- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
