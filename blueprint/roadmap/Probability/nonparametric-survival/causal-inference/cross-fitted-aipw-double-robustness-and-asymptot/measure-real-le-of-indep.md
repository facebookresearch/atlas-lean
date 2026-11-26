# Conditional Chebyshev bound for a split-sample empirical process term

Let $(\Omega, P)$ be a probability space, $\mathcal{U}, \mathcal{W}$ measurable spaces, $\nu$ a probability measure on $\mathcal{W}$, $s$ a finite index set and $c \in \mathbb{R}$ with $\lvert s \rvert \le c$. Let $U : \Omega \to \mathcal{U}$ and $V_i : \Omega \to \mathcal{W}$ be measurable such that, for $i, j \in s$, $V_i$ has law $\nu$ and is independent of $U$, and for $i \ne j$, $V_j$ is independent of $(U, V_i)$. Let $\Delta : \mathcal{U} \times \mathcal{W} \to \mathbb{R}$ be measurable with $\Delta(u, \cdot) \in L^2(\nu)$ for every $u$, and put $r(u) = \int \Delta(u, w)^2 \, d\nu(w)$. Then for all $\delta > 0$ and $\eta > 0$,

$$P\Bigl(\delta \le \Bigl\lvert c^{-1/2} \sum_{i \in s} \Bigl(\Delta(U, V_i) - \int \Delta(U, w)\, d\nu(w)\Bigr) \Bigr\rvert\Bigr) \le P\bigl(\eta \le r(U)\bigr) + \frac{\eta}{\delta^2}.$$

When $s$ is empty the sum is $0$, so the left side is $0$; when $c = 0$ the factor $c^{-1/2}$ is $0$ by the convention $0^{-1} = 0$.
