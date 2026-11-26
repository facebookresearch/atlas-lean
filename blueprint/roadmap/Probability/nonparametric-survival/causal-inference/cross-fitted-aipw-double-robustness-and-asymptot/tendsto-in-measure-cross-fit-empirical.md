# Cross-fitting removes the Donsker condition

Let $(\Omega, P)$ be a probability space, $\mathcal{W}$ a measurable space with a probability measure $\nu$, and for each $n \in \mathbb{N}$ a measurable space $\mathcal{U}_n$, a finite index set $s_n$ and a real $c_n \ge \lvert s_n \rvert$. Let $U_n : \Omega \to \mathcal{U}_n$ and $V_i : \Omega \to \mathcal{W}$ be measurable and assume, for every $n$ and $i, j \in s_n$: $V_i$ has law $\nu$ and is independent of $U_n$, and for $i \ne j$, $V_j$ is independent of $(U_n, V_i)$. Let $\Delta_n : \mathcal{U}_n \times \mathcal{W} \to \mathbb{R}$ be measurable with $\Delta_n(u, \cdot) \in L^2(\nu)$ for every $u$. If the conditional $L^2$ error tends to $0$ in probability,

$$\int \Delta_n(U_n, w)^2 \, d\nu(w) \xrightarrow{P} 0,$$

then the centered split-sample empirical process term tends to $0$ in probability:

$$c_n^{-1/2} \sum_{i \in s_n} \Bigl(\Delta_n(U_n, V_i) - \int \Delta_n(U_n, w)\, d\nu(w)\Bigr) \xrightarrow{P} 0.$$

No entropy or Donsker condition on the kernels is assumed.

For an empty fold $s_n$ the sum is $0$, and when $c_n = 0$ the factor $c_n^{-1/2}$ is $0$ by the convention $0^{-1} = 0$.
