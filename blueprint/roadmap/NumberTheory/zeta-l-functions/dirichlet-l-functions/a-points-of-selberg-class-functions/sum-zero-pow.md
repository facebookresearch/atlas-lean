# Landau-type formula for the zeros of the k-th derivative (Theorem 2, zeros case)

Let $F$
be a function in the Selberg class with Dirichlet coefficients $a(n)$, write $F^{(k)}$ for the
$k$-th derivative of $F$, let $k \ge 1$, let $\ell \ge 2$ be such that $a(\ell) \ne 0$ and
$a(n) = 0$ for $2 \le n < \ell$, and let $x > 1$ be real. Let $E_1$, $E_2$ and $\tau$ be real
numbers such that $F^{(k)}(s) \ne 0$ whenever $\operatorname{Re} s \ge E_1$, and whenever
$\operatorname{Re} s \le E_2$ and $|\operatorname{Im} s| \ge \tau$. Put

$$c = \sum_{l \ge 0} \sum_{n_0, \dots, n_l} \left(\frac{-1}{a(\ell) (\log \ell)^k}\right)^{l+1}
(\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k a(n_0) \cdots a(n_l),$$

the inner sum over the natural numbers $n_0 \ge \ell$ and $n_1, \dots, n_l \ge \ell + 1$ with
$n_0 \cdots n_l = x \ell^{l+1}$ (a finite sum, since $n_0 \cdots n_l \ge \ell (\ell + 1)^l$).
Then, as $T \to \infty$,

$$\sum_{\rho} m(\rho) x^{\rho} = \frac{T}{2\pi} c + O(\log T),$$

where $\rho$ runs over the zeros of $F^{(k)}$ with $E_2 < \operatorname{Re} \rho < E_1$ and
$0 < \operatorname{Im} \rho < T$, and $m(\rho)$ is the order of the zero of $F^{(k)}$ at $\rho$.

The paper takes $E_1$, $E_2$, $\tau$ from Lemmas 1 and 3. Its closing remark that the sum is
empty when $\ell^n x \notin \mathbb{Z}$ for all $n$ is not stated separately.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Theorem 2 (`integers-2024-A11-thm-2`).
