# The cross-fitting variance identity

Let $(\Omega, P)$ be a probability space, $\mathcal{U}$ and $\mathcal{W}$ measurable spaces, $\nu$ a probability measure on $\mathcal{W}$, and $s$ a finite index set. Let $U : \Omega \to \mathcal{U}$ (training data) and $V_i : \Omega \to \mathcal{W}$ (evaluation units) be measurable, and assume for $i, j \in s$:

- $V_i$ has law $\nu$ and is independent of $U$;
- for $i \ne j$, $V_j$ is independent of the pair $(U, V_i)$.

Let $D : \mathcal{U} \times \mathcal{W} \to \mathbb{R}$ be measurable, centered in its second argument, $\int D(u, w)\, d\nu(w) = 0$ for every $u$, and with $D^2$ integrable for $P_U \otimes \nu$, where $P_U$ is the law of $U$. Then

$$\mathbb{E}\Bigl[\Bigl(\sum_{i \in s} D(U, V_i)\Bigr)^2\Bigr] = \lvert s \rvert \int D^2 \, d(P_U \otimes \nu).$$

The cross terms vanish from independence alone; no entropy or Donsker condition is used.
