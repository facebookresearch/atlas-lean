# Cheeger's inequality for reversible Markov chains, upper bound

Let $P$ be a stochastic matrix, reversible with respect to a probability vector $\pi > 0$, and let $\Phi \ge 0$ be at most the conductance: $\Phi\,\pi(A) \le Q(A,A^c) = \sum_{u \in A,\ v \notin A}\pi(u)P(u,v)$ whenever $0 < \pi(A) \le 1/2$. Then every real eigenvalue $\mu \ne 1$ of $P$ satisfies $\mu \le 1 - \Phi^2/2$. This is Lemma 3.3 of A. Sinclair and M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov chains*, Information and Computation 82 (1989), 93–133 (for ergodic reversible chains), restated as the upper half of Theorem 2 of A. Sinclair, *Combinatorics, Probability and Computing* 1 (1992). Together with [Sinclair's Theorem 3](sum-le-two-mul-of-path-load-le.md) it yields his Corollary 4, $\lambda_1 \le 1 - 1/(8\rho^2)$.

## Background

- [Cheeger's inequality, hard direction](../../../GraphTheory/algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/exists-threshold-cut-le-sqrt.md): the analogous inequality for weighted graphs. Sinclair identifies a reversible chain with the graph whose edge $\{u,v\}$ has weight $\pi(u)P(u,v)$ and describes $\Phi$ as a weighted version of its edge expansion.
