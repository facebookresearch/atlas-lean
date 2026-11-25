# Uniform law of large numbers for a finite-rank log-likelihood

Let the log-likelihood have finite rank: $\ell_\theta(x) = \sum_{j<m}a_j(\theta)g_j(x)$. If each $a_j$ is bounded on $K$, each $g_j$ is measurable with $g_j(X_0)$ integrable, and the observations $X_i$ are pairwise independent and identically distributed, then almost surely $\frac1n\sum_{i<n}\ell_\theta(X_i) \to \mathbb{E}[\ell_\theta(X_0)]$ uniformly in $\theta \in K$.
