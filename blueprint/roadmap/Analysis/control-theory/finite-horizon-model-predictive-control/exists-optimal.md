# Existence of an optimal input sequence in finite-horizon control

Let $X$ and $U$ be topological spaces with $U$ Hausdorff, and let $f : X \times U \to X$ be jointly continuous discrete-time dynamics. Let $U_s \subseteq U$ be compact, let $X_s, X_f \subseteq X$ be closed, let the stage cost $\ell : X \times U \to \mathbb{R}$ be jointly continuous and the terminal cost $V : X \to \mathbb{R}$ be continuous, and fix an initial state $x_0$ and a horizon $N$. If some input sequence $u : \{0,\dots,N-1\} \to U$ is feasible (inputs in $U_s$, states $x_k \in X_s$ for $k < N$, terminal state $x_N \in X_f$), then there is a feasible input sequence $u^\ast$ with

$$J_N(x_0, u^\ast) \le J_N(x_0, v)$$

for every feasible $v$, where $J_N(x_0, v) = \sum_{k<N} \ell(x_k(v), v_k) + V(x_N(v))$.
