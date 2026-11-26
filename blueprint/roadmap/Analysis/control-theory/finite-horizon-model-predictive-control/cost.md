# Cost of an input sequence over a finite horizon

Let $f : X \to U \to X$ be discrete-time dynamics with initial state $x_0$, let $\ell : X \to U \to \mathbb{R}$ be a stage cost and $V : X \to \mathbb{R}$ a terminal cost, and let $N \in \mathbb{N}$. The $N$-step cost of an input sequence $u : \{0,\dots,N-1\} \to U$ with trajectory $x_k = x_k(u)$ is

$$J_N(x_0, u) = \sum_{k=0}^{N-1} \ell(x_k, u_k) + V(x_N).$$
