# Coherence implies the Exact Recovery Condition

Let $(D_i)_{i \in \kappa}$ be a dictionary of unit vectors in an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ with coherence at most $\mu$: $|\langle D_i, D_j\rangle| \le \mu$ for $i \ne j$. Let $\Lambda$ be a finite set of $m$ indices with

$$(2m - 1)\,\mu < 1 .$$

For $\mu > 0$ this reads $m < \tfrac12(\mu^{-1} + 1)$; for $\mu = 0$ (an orthonormal dictionary) it holds for every $m$.

Then the Exact Recovery Condition holds for $\Lambda$: for every $\omega \notin \Lambda$ there are coefficients $a$ with $\sum_{i \in \Lambda} a_i D_i = P_K D_\omega$, where $K = \operatorname{span}\{D_i : i \in \Lambda\}$, and $\sum_{i \in \Lambda} |a_i| < 1$. Tropp proves the sharper sufficient condition $\mu_1(m-1) + \mu_1(m) < 1$ for the cumulative coherence $\mu_1$, using a Neumann series for the inverse Gram matrix; with $\mu_1(k) \le k\mu$ it gives the statement here. Combined with the greedy step, OMP then recovers every $m$-term superposition.

## Sources

- J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004), 2231–2242, DOI 10.1109/TIT.2004.834793, Theorem 3.5 and Corollary 3.6.
