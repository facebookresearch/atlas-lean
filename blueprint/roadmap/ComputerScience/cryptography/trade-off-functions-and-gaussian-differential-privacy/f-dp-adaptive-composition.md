# Lossless adaptive composition of f-differential privacy

Let $M_1, \dots, M_k$ be mechanisms applied adaptively to the same dataset, where $M_i$ may depend on the outputs of $M_1, \dots, M_{i-1}$ and is $f_i$-DP for every fixed value of those outputs. Then the joint mechanism $(M_1, \dots, M_k)$ is $f_1 \otimes \cdots \otimes f_k$-DP, and this bound is tight in general. In particular the $k$-fold adaptive composition of $\mu$-GDP mechanisms is $\sqrt{k}\,\mu$-GDP, and the composition of $\mu_i$-GDP mechanisms is $\sqrt{\sum_i \mu_i^2}$-GDP.

## Proof sketch

For two mechanisms, fix a neighbouring pair; conditionally on the first output $y$, the second mechanism's output distributions have trade-off at least $f_2$, so by a coupling (Blackwell) argument there is a Markov kernel mapping the pair $(P_2, Q_2)$ representing $f_2$ to the conditional outputs. Hence the joint outputs are a post-processing of the product pair representing $f_1 \otimes f_2$, and post-processing increases trade-off functions. Induction gives the general case; the Gaussian formula follows from $G_{\mu_1} \otimes G_{\mu_2} = G_{\sqrt{\mu_1^2+\mu_2^2}}$, a rotation of a two-dimensional Gaussian test.

## Depends on

- [Tensor product of trade-off functions](tensor-product-of-trade-off-functions.md)

## Proof depends on

- [Characterization of trade-off functions](trade-off-function-characterization.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
