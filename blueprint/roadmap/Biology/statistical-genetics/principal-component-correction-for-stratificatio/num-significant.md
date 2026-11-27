# Sequential count of significant axes

For a sequence of real statistics $(T_k)_{k \ge 0}$ and a threshold $t \in \mathbb{R}$, the sequential count $n_t(K)$ of significant axes among the first $K$ is defined by

$$n_t(0) = 0, \qquad n_t(K + 1) = \begin{cases} K + 1 & \text{if } n_t(K) = K \text{ and } T_K > t,\\ n_t(K) & \text{otherwise}. \end{cases}$$

It is the length of the leading run of statistics exceeding $t$ among $T_0, \dots, T_{K-1}$: testing stops at the first non-significant statistic, as in the sequential rule of Patterson, Price and Reich (2006).

## Sources

- N. Patterson, A. L. Price and D. Reich, *Population structure and eigenanalysis*, PLoS Genet. 2 (2006), e190.
