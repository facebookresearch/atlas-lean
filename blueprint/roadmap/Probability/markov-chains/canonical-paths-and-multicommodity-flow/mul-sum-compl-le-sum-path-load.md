# Paths crossing a cut

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$ with $\pi(x) \ge 0$ for every $x$, and for each
pair $x \ne y$ let $\gamma_{xy}$ be a path from $x$ to $y$. Then for every set $A \subseteq S$,

$$\pi(A)\, \pi(A^c) \le \sum_{u \in A} \sum_{v \notin A} L(u, v),$$

where $\pi(A) = \sum_{x \in A} \pi(x)$ and $L(u, v)$ is the [load](path-load.md) of the oriented
edge $(u, v)$: all flow from $A$ to its complement crosses the cut.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, proof of Theorem 3.
