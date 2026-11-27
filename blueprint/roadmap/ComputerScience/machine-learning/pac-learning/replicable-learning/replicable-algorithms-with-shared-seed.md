# Replicable algorithms with shared randomness

A randomized sample algorithm $A$ with sample size $m$, domain $X$, seed space $\Omega$ and output set $\mathcal{Y}$ consists of a seed distribution $\pi$ on $\Omega$ and, for each sample $S \in X^m$ and seed $\omega \in \Omega$, an output distribution $A(S, \omega)$ on $\mathcal{Y}$. For a distribution $D$ on $X$, its disagreement probability $\mathrm{dis}_D(A)$ is the probability that $y_1 \ne y_2$ when $S_1, S_2 \sim D^m$ are independent, $\omega \sim \pi$ is shared, and $y_j \sim A(S_j, \omega)$ independently. $A$ is $\rho$-replicable over a family $\mathcal{D}$ of distributions if $\mathrm{dis}_D(A) \le \rho$ for every $D \in \mathcal{D}$, and strongly $\rho$-replicable if this holds for all distributions on $X$. Given acceptable output sets $\mathrm{good}(D) \subseteq \mathcal{Y}$, $A$ is $\beta$-accurate over $\mathcal{D}$ if for every $D \in \mathcal{D}$ a single run outputs outside $\mathrm{good}(D)$ with probability at most $\beta$; for real outputs, $A$ is an $(\varepsilon, \beta)$-estimator of $\tau(D)$ if $\mathrm{good}(D) = [\tau(D) - \varepsilon, \tau(D) + \varepsilon]$.

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
