# Tutte's perfect matching criterion via odd components of vertex deletions

Let $G$ be a simple graph on a finite vertex set $V$. For $u \subseteq V$ let $o(G - u)$ be the number of connected components with an odd number of vertices of the graph obtained from $G$ by deleting $u$, and call $u$ a *Tutte violator* when $|u| < o(G - u)$. Then $G$ has a perfect matching if and only if no subset $u \subseteq V$ is a Tutte violator, that is,

$$
o(G - u) \le |u| \qquad \text{for every } u \subseteq V .
$$

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: [SimpleGraph.tutte](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Combinatorics/SimpleGraph/Tutte.lean#L316 "SimpleGraph.tutte").
- W. T. Tutte, "The factorization of linear graphs", Journal of the London Mathematical Society 22 (1947).
