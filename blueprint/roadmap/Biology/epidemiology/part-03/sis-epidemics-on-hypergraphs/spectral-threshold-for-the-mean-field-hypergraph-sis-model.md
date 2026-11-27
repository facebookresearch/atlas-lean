# Spectral threshold for the mean-field hypergraph SIS model

Let $H = (V, E)$ be a hypergraph with $n$ nodes and $m$ hyperedges, incidence matrix $I \in \{0,1\}^{n\times m}$ ($I_{ih} = 1$ iff node $i$ lies in hyperedge $h$), and $W = I I^{\top}$, so $W_{ij}$ counts the hyperedges containing both $i$ and $j$. In the hypergraph SIS model a susceptible node $i$ becomes infected at rate $\beta \sum_{h} I_{ih}\, f\big(\sum_j X_j I_{jh}\big)$, where $X_j \in \{0,1\}$ is the infection state, $f : \mathbb{R}_+ \to \mathbb{R}_+$ satisfies $f(0) = 0$ and is $C^1$ near $0$, and infected nodes recover at rate $\delta > 0$. The **mean-field approximation** for $p_i(t) \approx \Pr(X_i(t) = 1)$ is

$$\dot p_i = \beta \sum_{h} I_{ih}\, f\Big(\sum_j p_j I_{jh}\Big)(1 - p_i) - \delta p_i, \qquad p_i(0) \in [0,1].$$

Let $\lambda(W)$ denote the largest eigenvalue of the symmetric matrix $W$.

**Theorem (local).** If $\lambda(W)\, f'(0)\, \beta / \delta < 1$, the disease-free state $p = 0$ is locally asymptotically stable.

**Theorem (global, concave case).** If in addition $f$ is concave, then $p(t) \to 0$ for every initial condition in $[0,1]^n$.

**Partitioned version.** If the hyperedges are split into $K$ categories with incidence matrices $I^{(k)}$, $W^{(k)} = I^{(k)} I^{(k)\top}$, and category-specific concave infection functions $f_k$, the same conclusions hold under

$$\lambda\Big(\sum_{k=1}^{K} f_k'(0)\, W^{(k)}\Big)\, \frac{\beta}{\delta} < 1 .$$

For $f(x) = x$ the model is SIS on the weighted clique graph of $H$ and the condition becomes the classical graph threshold $\lambda(W)\beta/\delta < 1$, here given a rigorous mean-field proof; for the stochastic SIS process on a graph the same quantity governs fast die-out (Ganesh, Massoulié and Towsley 2005).

## Expansion

The Jacobian at $0$ is $\beta f'(0) W - \delta I_n$, symmetric with largest eigenvalue $\beta f'(0)\lambda(W) - \delta < 0$, giving local stability. For the global statement, write the Jacobian at any $P$ as $B - \Lambda$ with $\Lambda = \operatorname{diag}\big(\beta \sum_h I_{ih} f(\sum_j p_j I_{jh})\big) \ge 0$ and $B_{ij} = \beta \sum_h I_{ih} I_{jh} f'(\cdot)(1-p_i) - \delta\,\mathbf 1[i=j]$. Subtracting a non-negative diagonal cannot raise the top eigenvalue of the symmetric part, and concavity gives $f'(x) \le f'(0)$, so the non-negative matrix $B^{(S)} + \delta I$ is entrywise dominated by $\beta f'(0) W$; Perron–Frobenius then bounds $\lambda\big((\nabla g(P))^{(S)}\big) \le \beta f'(0)\lambda(W) - \delta < 0$ uniformly in $P$, which yields global convergence by a contraction (logarithmic-norm) argument. Concavity covers saturating pressures such as $\arctan x$ and $\min(x,c)$; threshold-type collective contagion functions are not concave and need a separate treatment.

## Sources

- D. J. Higham, H.-L. de Kergorlay, "Epidemics on hypergraphs: spectral thresholds for extinction", Proceedings of the Royal Society A 477 (2021) 20210232, Eqs. (3.1), (3.2), (4.1), Theorems 6.1, 6.2, 6.5, 6.6 and Lemma 6.4, <https://doi.org/10.1098/rspa.2021.0232>, PMCID PMC8355667.
