# Landau-type formula for the a-points of the k-th derivative (Theorem 2, a ≠ 0)

Let $F$ be
a function in the Selberg class with Dirichlet coefficients $a_F(n)$, write $F^{(k)}$ for the
$k$-th derivative of $F$, let $k \ge 1$, let $a \ne 0$ be a complex number and let $x > 1$ be
real. Let $E_1$, $E_2$ and $\tau$ be real numbers such that $F^{(k)}(s) \ne a$ whenever
$\operatorname{Re} s \ge E_1$, and whenever $\operatorname{Re} s \le E_2$ and
$|\operatorname{Im} s| \ge \tau$. Put

$$c = \sum_{l \ge 0} \sum_{n_0 \cdots n_l = x} \frac{(-1)^{k(l+1)}}{a^{l+1}} (\log n_0)^{k+1}
(\log n_1 \cdots \log n_l)^k a_F(n_0) \cdots a_F(n_l),$$

the inner sum over the natural numbers $n_0, \dots, n_l \ge 1$ with product $x$ (only finitely
many terms are nonzero, since a term vanishes when some $n_i = 1$). Then, as $T \to \infty$,

$$\sum_{\rho} m(\rho) x^{\rho} = \frac{T}{2\pi} c + O(\log T),$$

where $\rho$ runs over the points with $F^{(k)}(\rho) = a$, $E_2 < \operatorname{Re} \rho < E_1$
and $0 < \operatorname{Im} \rho < T$, and $m(\rho)$ is the order of the zero of $F^{(k)} - a$ at
$\rho$.

The paper takes $E_1$, $E_2$, $\tau$ from Lemmas 1 and 3 and restricts to $n_i \ge \ell$, where
$\ell \ge 2$ is least with $a_F(\ell) \ne 0$; the added terms vanish. Its closing remark that the
sum is empty for $x \notin \mathbb{Z}$ is immediate from the condition on the $n_i$.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Theorem 2 (`integers-2024-A11-thm-2`).
