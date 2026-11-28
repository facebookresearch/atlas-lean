# Wasserstein distance under an independent shift and a scaling

Discounting by $\gamma \in [0,1]$ and adding an independent reward multiplies the $p$-Wasserstein distance between laws with finite $p$-th moments by at most $\gamma$.

Let $1 \le p < \infty$, $\gamma \in [0,1]$, $S_\gamma(t) = \gamma t$, and let $\rho, \nu, \mu \in \mathscr{P}_p(\mathbb{R})$ be Borel probability measures on $\mathbb{R}$ with finite $p$-th moments. Then, with $W_p$ the [Wasserstein distance of order $p$](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md), $(S_\gamma)_\#$ the [law](../../../../../Probability/foundations/probability-measures/probability-measure-map.md) of the scaled variable and $*$ the [convolution](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/conv.md),

$$W_p\bigl(\rho * (S_\gamma)_\# \nu, \; \rho * (S_\gamma)_\# \mu\bigr) \le \gamma \, W_p(\nu, \mu).$$

In random-variable form: if $R \sim \rho$ is independent of $U \sim \nu$ and of $V \sim \mu$, then $W_p(\mathrm{Law}(R + \gamma U), \mathrm{Law}(R + \gamma V)) \le \gamma \, W_p(\nu, \mu)$. Bellemare, Dabney and Munos display this combined form in the proof of the contraction of the distributional Bellman operator, in their space of value distributions with all moments bounded; the statement here, for laws with finite $p$-th moments, is supported by the linked main lemmas on scaling and on sums of independent variables, which hold for all laws.

## Depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Law of a random element](../../../../../Probability/foundations/probability-measures/probability-measure-map.md)
- [Convolution of probability measures](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/conv.md)

## Proof depends on

- [Scaling of the Mallows metric](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/wasserstein-map-smul.md)
- [Mallows metric of sums of independent variables](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/wasserstein-conv-le.md)
- [The Wasserstein distance vanishes on the diagonal](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-self.md)

## Expansion

By the [convolution inequality](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/wasserstein-conv-le.md), $W_p(\rho * \nu', \rho * \mu') \le W_p(\rho, \rho) + W_p(\nu', \mu')$, and $W_p(\rho, \rho) = 0$. By the [scaling identity](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/wasserstein-map-smul.md), $W_p((S_\gamma)_\# \nu, (S_\gamma)_\# \mu) = \gamma \, W_p(\nu, \mu)$. Combining the two with $\nu' = (S_\gamma)_\# \nu$ and $\mu' = (S_\gamma)_\# \mu$ gives the display. A coupling proof also works: take a coupling $(U, V)$ of $\nu$ and $\mu$ and a fresh $R \sim \rho$ independent of the pair; then $(R + \gamma U, R + \gamma V)$ couples the two convolutions at cost $\gamma^p \mathbb{E}|U - V|^p$. Independence of $R$ from each of $U$ and $V$ already identifies both convolution laws; independence from the pair is a convenient way to build the coupling. Bellemare, Dabney and Munos state the two ingredients as properties (P1), scaling by a real scalar, and (P2), adding an independent variable, and display the combination in the first step of their proof of Lemma 3; the two ingredients on main are stated for all laws. Their property (P3), a bound for products with an independent random factor, is not used in this topic.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2, properties (P1) and (P2), and Appendix B, proof of Lemma 3 (first inequality).
