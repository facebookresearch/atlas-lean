# Storey's theorem: pFDR is a posterior null probability

Let $m \ge 1$ and $q : \{0,1\}^2 \to \mathbb{R}$ with $q \ge 0$. Then

$$\mathrm{pFDR}(q, m) = \frac{q(1, 1)}{q(1, 1) + q(0, 1)},$$

where $q(1,1) = P(H = 0, T \in \Gamma)$ and $q(0,1) = P(H = 1, T \in \Gamma)$ for a test rejecting when its statistic lies in $\Gamma$: $\mathrm{pFDR} = P(H = 0 \mid T \in \Gamma)$ (Storey 2002, Theorem 1). The identity is homogeneous in $q$, so only $q \ge 0$ is assumed; when $q(1,1) + q(0,1) = 0$ both sides are $0$.
