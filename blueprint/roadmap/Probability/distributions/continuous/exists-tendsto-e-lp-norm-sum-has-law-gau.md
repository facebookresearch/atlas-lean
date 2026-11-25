# Series of independent centered Gaussians

Let $(\Omega, P)$ be a probability space and let $(X_k)_{k \in \mathbb{N}}$ be mutually independent real random variables with $X_k \sim \mathcal{N}(0, v_k)$, where $v_k \ge 0$ and $\sum_k v_k < \infty$. Then there is a random variable $S : \Omega \to \mathbb{R}$ such that the partial sums converge to $S$ in $L^2(P)$,

$$\Big\lVert S - \sum_{k < n} X_k \Big\rVert_{L^2(P)} \longrightarrow 0 \quad (n \to \infty),$$

and $S$ has law $\mathcal{N}\big(0, \sum_{k=0}^\infty v_k\big)$.
