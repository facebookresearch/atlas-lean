# Type counts in binary Galton–Watson trees with mutation and reversion

**Model.** Every node of a random binary tree carries a type $j \in \{0,1,2,\dots\}$ (the number of accumulated mutations). In discrete time a node has no offspring with probability $q$ and two offspring with probability $p = 1 - q$; the two offspring of a type-$j$ node have types $0$ (wild type or revertant) and $j+1$ (one more mutation). In continuous time each node splits in the same way after an independent $\operatorname{Exp}(\lambda)$ time (a Yule tree $\mathcal{T}_t$ observed at time $t$). Let $S$ be the number of non-root nodes with nonzero type (equivalently the number of splits; the total progeny is $1 + 2S$), $X^{(k)}$ the number of non-root nodes of type $k \ge 1$, $C_n = \frac{1}{n+1}\binom{2n}{n}$ the Catalan numbers, and $\mathbb{P}_j$ the law started from a root of type $j$.

**Theorem.**
1. *(Discrete time.)* $\mathbb{P}(S = n) = q\,(pq)^n C_n$ for $n \ge 0$, with $\mathbb{E}[\delta^S] = \dfrac{1 - \sqrt{1 - 4pq\delta}}{2p\delta}$; $S < \infty$ a.s. iff $p \le 1/2$, and then (for $p < 1/2$) $\mathbb{E}S = p/(q - p)$.
2. *(Continuous time.)* The number $N_t$ of nonzero-type nodes in $\mathcal{T}_t$ is geometric: $\mathbb{P}(N_t = m) = e^{-\lambda t}(1 - e^{-\lambda t})^m$.
3. *(Conditional types.)* Given $S = m$, the type configuration is uniform over the $C_m$ binary tree shapes with $m$ splits, so the conditional law of $(X^{(1)}, \dots, X^{(n)})$ does not depend on $p, q$; in particular, for $l, m \ge 1$,

$$\mathbb{E}_j\big[X^{(l)} \mid S = m\big] = \frac{1}{C_m}\left(\mathbf{1}\{0 < l - j \le m\}\,\frac{l - j + 1}{m+1}\binom{2m - l + j}{m} + \mathbf{1}\{m \ge l\}\binom{2m - l}{m+1}\right).$$

4. *(Long-run proportions.)* For $0<p<1/2$, with the incomplete beta function $B(z; a, b) = \int_0^z u^{a-1}(1-u)^{b-1}du$,

$$\mathbb{E}_j\left[\frac{X^{(k)}}{S}\,\Big|\, S \ge 1\right] = \frac{q}{p}B(p; k+1, -1) + \frac{q}{p}\,\mathbf{1}\{k > j\}\Big((k+1-j)\,B(p; k - j, 0) - \frac{p^{k-j}}{q}\Big).$$

## Expansion

Since every split creates exactly one nonzero-type child, $S$ is the number of internal nodes of a binary Galton–Watson tree, whose law is $q(pq)^nC_n$ by counting binary trees with $n$ internal nodes; the generating function solves $G = q + p\delta G^2$. Given the shape, types are deterministic: along each path a node's type is the number of consecutive "mutant" steps since the last "wild type" step, so counting type-$l$ nodes reduces to counting binary trees with marked right paths of length $l$, giving ballot-type binomial expressions. The continuous-time tree conditioned on its number of splits has the same uniform shape, and its split count at time $t$ is the geometric Yule count.

## Sources

- Q. Huang and N. Privault, "Binary Galton–Watson trees with mutations", *Communications in Nonlinear Science and Numerical Simulation* 156 (2026), 109623, Propositions 2.1, 3.1, Theorem 2.2 and Corollaries 2.3, 2.4, <https://doi.org/10.1016/j.cnsns.2025.109623> (preprint arXiv:2501.10951).
