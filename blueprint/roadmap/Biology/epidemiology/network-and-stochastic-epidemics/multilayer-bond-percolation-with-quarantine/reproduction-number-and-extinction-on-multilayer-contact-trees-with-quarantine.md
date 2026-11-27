# Reproduction number and extinction probability on multilayer contact trees with quarantine

The contact structure is a tree $T$ whose edges are split into $n$ classes, each class forming a tree $T_i$ on the same vertices. A random vertex has independent class degrees $k_i$ with distributions $P_i$ and generating functions $G_i(x) = \sum_k P_i(k)x^k$, so the joint generating function is $G(x_1,\dots,x_n) = \prod_i G_i(x_i)$, $E(k_i) = G_i'(1)$ and $E(k) = \sum_i E(k_i)$. Transmission along a class-$i$ edge happens independently with probability $T_i$. Each infected individual is detected and completely isolated, before transmitting, with probability $Q$.

Let $Z(x)$ be the generating function of the number infected by patient zero and $\tilde Z(x)$ that for an individual reached along a random edge (using the excess-degree distribution, with the infecting edge removed). Without quarantine, $\tilde Z = \tilde Z_{\mathrm{free}}$, and with quarantine $\tilde Z = Q + (1-Q)\tilde Z_{\mathrm{free}}$.

**Proposition 1 (reproduction number).** $R_0 = \tilde Z'(1) = (1-Q)\,R_0^{\mathrm{free}}$, and for independent layer degrees

$$R_0 = (1-Q)\sum_{j=1}^n T_j\,E(k_j)\left(1 - \frac{1}{\sum_l E(k_l)}\right) + (1-Q)\sum_{j=1}^n T_j\,\frac{\sigma(k_j)^2}{\sum_l E(k_l)},$$

where $\sigma(k_j)^2$ is the variance of the class-$j$ degree.

**Proposition 2 and Theorems 3–4 (extinction).** The probability $P_\infty$ that the chain started from an individual reached along an edge dies out is the smallest fixed point of $\tilde Z$ in $[0,1]$; excluding the degenerate case $\tilde Z(x) \equiv x$ (every reached individual infects exactly one other), $\tilde Z$ has at most two fixed points in $[0,1]$. The probability that the outbreak from patient zero dies out is $P = Z(P_\infty)$. In the nondegenerate case, if $R_0 \le 1$ then $P = P_\infty = 1$; if $R_0 > 1$ and $\tilde Z(0) > 0$ (for instance $Q > 0$) then $P_\infty, P \in (0,1)$. In all cases $P_\infty \ge Q$ and $P \ge Q$.

**Corollary (containment by isolation).** Excluding the degenerate case $\tilde Z \equiv x$, the outbreak dies out almost surely if and only if $Q \ge 1 - 1/R_0^{\mathrm{free}}$. For example, $R_0^{\mathrm{free}} = 3$ requires isolating at least $2/3$ of the infected.

## Expansion

An individual reached along a class-$i$ edge has that edge's class-$i$ excess degree and unchanged degrees in the other classes. It is reached via class $i$ with probability $E(k_i)/E(k)$. Summing the expected number of onward transmissions $T_j$ per edge over the excess-degree means $E(k_j) - \delta_{ij} + \delta_{ij}\sigma(k_j)^2/E(k_j)$ gives the formula: the variance term shows that heterogeneity in any single layer inflates $R_0$ in proportion to that layer's transmissibility. Isolation multiplies every non-trivial offspring event by $1-Q$, so it scales $R_0$ linearly. The fixed-point statements are the Galton–Watson dichotomy, proved here from convexity of $\tilde Z$: $f(x) = x - \tilde Z(x)$ is strictly concave, so it has at most one zero in $(0,1)$, which exists exactly when $f'(1) = 1 - R_0 < 0$. The single-layer case recovers the classical bond-percolation results for configuration-model networks.

## Sources

- G. Oliveira, "Early epidemic spread, percolation and Covid-19", Journal of Mathematical Biology (2020), Sections 2–4, Eqs. (2.1)–(2.4), Propositions 1–2, Remarks 3–4 and Theorems 3–4, <https://doi.org/10.1007/s00285-020-01539-1>, PMCID PMC7499022.
