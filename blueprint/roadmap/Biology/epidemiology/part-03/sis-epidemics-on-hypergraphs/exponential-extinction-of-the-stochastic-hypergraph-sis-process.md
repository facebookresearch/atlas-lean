# Exponential extinction of the stochastic hypergraph SIS process

Consider the exact continuous-time Markov hypergraph SIS process of [Spectral threshold for the mean-field hypergraph SIS model](spectral-threshold-for-the-mean-field-hypergraph-sis-model.md): node states $X_i(t) \in \{0,1\}$, infection rate $\beta \sum_h I_{ih} f(\sum_j X_j I_{jh})$ for susceptible node $i$, recovery rate $\delta$, and $W = I I^{\top}$. Assume $f$ is concave with $f(0) = 0$, and that initially each node is infected independently with probability $i_0$.

**Theorem.** For all $t \ge 0$,

$$\Pr\Big(\sum_i X_i(t) > 0\Big) \le n\, i_0\, \exp\!\big((\beta f'(0)\lambda(W) - \delta)\, t\big).$$

Hence if $\lambda(W) f'(0)\beta/\delta < 1$ the infection dies out exponentially fast.

**Corollary.** Under the same condition the extinction time $\tau$ satisfies

$$\mathbb{E}[\tau] \le \frac{\log n + 1}{\delta - f'(0)\beta\lambda(W)} .$$

With $K$ categories of hyperedges and concave $f_k$, the same bounds hold with $f'(0)\lambda(W)$ replaced by $\lambda\big(\sum_k f_k'(0) W^{(k)}\big)$.

## Depends on

- [Spectral threshold for the mean-field hypergraph SIS model](spectral-threshold-for-the-mean-field-hypergraph-sis-model.md)

## Expansion

Concavity and $f(0) = 0$ give $f(x) \le f'(0)x$, so the infection rate of node $i$ is at most $\beta f'(0) \sum_j W_{ij} X_j$. Couple $X$ with an auxiliary linear birth–death process $Y \in \mathbb{N}^n$ with birth rate $\beta f'(0)\sum_j W_{ij} Y_j$ and death rate $\delta Y_i$ at node $i$; $Y$ dominates $X$. The means $q = \mathbb{E}[Y]$ solve the linear system $\dot q = (\beta f'(0) W - \delta I) q$, so $\|q(t)\|_2 \le e^{(\beta f'(0)\lambda(W) - \delta)t}\|q(0)\|_2$ since the matrix is symmetric. Markov's inequality and Cauchy–Schwarz ($\sum_i q_i \le \sqrt n \|q\|_2$, $\|q(0)\|_2 = \sqrt n\, i_0$) give the bound. Integrating $\Pr(\tau > t) \le \min\{1, n e^{-(\delta - \beta f'(0)\lambda(W))t}\}$ and splitting at $t = \log n / (\delta - \beta f'(0)\lambda(W))$ gives the corollary, extending the graph result of Ganesh, Massoulié and Towsley to group interactions.

## Sources

- D. J. Higham, H.-L. de Kergorlay, "Epidemics on hypergraphs: spectral thresholds for extinction", Proceedings of the Royal Society A 477 (2021) 20210232, Section 8, Theorem 8.1, Corollary 8.2 and Theorem 8.3, <https://doi.org/10.1098/rspa.2021.0232>, PMCID PMC8355667.
