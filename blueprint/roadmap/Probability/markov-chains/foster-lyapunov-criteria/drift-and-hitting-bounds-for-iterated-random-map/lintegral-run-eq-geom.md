# Exact drift recursion for expectations along the chain

Let $D$ carry a probability law, let the inputs of the chain be independent with that law, and let $f : S \times D \to S$ be jointly measurable and $V : S \to [0, \infty]$ measurable. If one step satisfies $\mathbb{E}[V(f(x, d))] = \rho V(x) + \beta$ for every state $x$, with $\rho, \beta \in [0, \infty]$, then for every $n$ the expectation of $V$ at mark $n$ of the chain started at $x_0$ is exactly $\rho^n V(x_0) + \beta \sum_{k<n} \rho^k$.
