# Totally dual integral system

Let $A$ be a real $m \times n$ matrix and $b \in \mathbb{R}^m$. The system $A x \le b$ is *totally dual integral* if for every $c \in \mathbb{Z}^n$ such that the system is feasible and $c^\top x$ is bounded above on $\{x : A x \le b\}$, there are $y \in \mathbb{Z}^m$ with $y \ge 0$ and $A^\top y = c$, and a feasible $x$, with $b^\top y = c^\top x$. By weak duality such a $y$ is an optimal solution of the dual $\min\{b^\top y : y \ge 0,\ A^\top y = c\}$, and $x$ is optimal for the primal. Goemans states the definition for rational $A$ and $b$; the definition above allows real data, and the [Edmonds–Giles theorem](extreme-points-integral-of-is-tdi.md) assumes rational $A$.

## Sources

- M. X. Goemans, *Advanced Combinatorial Optimization*, MIT 18.438, Lecture 6 (2009), <https://math.mit.edu/~goemans/18438F09/lec6.pdf>, Definition 1.
- J. Edmonds and R. Giles, *A min-max relation for submodular functions on graphs*, Ann. Discrete Math. 1 (1977), 185–204.
