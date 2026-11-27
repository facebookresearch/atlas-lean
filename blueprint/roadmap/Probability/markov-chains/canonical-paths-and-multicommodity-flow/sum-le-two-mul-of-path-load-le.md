# Sinclair's Theorem 3: $\Phi \ge 1/(2\rho)$

Let $\pi$ be a probability vector, $\gamma_{xy}$ a path from $x$ to $y$ for each $x \ne y$, and $\rho$ a bound on every edge load: $\sum_{x \ne y}\pi(x)\pi(y)m_{xy}(u,v) \le \rho\,\pi(u)P(u,v)$. Then every set $A$ with $\pi(A) \le 1/2$ satisfies $\pi(A) \le 2\rho\, Q(A, A^c)$, where $Q(A,A^c) = \sum_{u \in A,\, v \notin A}\pi(u)P(u,v)$. Minimising over $0 < \pi(A) \le 1/2$, the conductance $\Phi = \min Q(A,A^c)/\pi(A)$ is at least $1/(2\rho)$: Theorem 3 of A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370. It follows from the cut bound $\pi(A)\pi(A^c) \le \rho\, Q(A,A^c)$ and $\pi(A^c) \ge 1/2$.

## Background

- [Cheeger's inequality for reversible Markov chains, upper bound](le-one-sub-sq-div-two-of-eigenvector.md): combined with this theorem it gives Sinclair's Corollary 4, $\lambda_1 \le 1 - 1/(8\rho^2)$.
