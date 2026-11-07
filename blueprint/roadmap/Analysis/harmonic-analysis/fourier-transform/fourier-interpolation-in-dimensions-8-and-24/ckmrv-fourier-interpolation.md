# Cohn–Kumar–Miller–Radchenko–Viazovska Fourier interpolation theorem

Let
$(n, k_0)$ be $(8, 1)$ or $(24, 2)$. For a complex-valued Schwartz function $f$ on
$\mathbb{R}^n$, let $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ be its
Fourier transform, let $e_1$ be the first standard basis vector and let $r_k = \sqrt{2k}$.
The sampling map sends $f$ to the four complex sequences indexed by the integers $k \ge k_0$
whose $k$-th terms are $f(r_k e_1)$, $\hat f(r_k e_1)$ and the derivatives at $r = r_k$ of
$r \mapsto f(r e_1)$ and of $r \mapsto \hat f(r e_1)$. Call $f$ radial if $f(x) = f(y)$
whenever $|x| = |y|$, and call a sequence $(a_k)_{k \ge k_0}$ rapidly decreasing if
$k^m |a_k| \to 0$ as $k \to \infty$ for every natural number $m$. Then the sampling map is a
bijection from the radial Schwartz functions on $\mathbb{R}^n$ onto the quadruples of rapidly
decreasing sequences indexed by $k \ge k_0$. So sampling starts at radius $\sqrt 2$ in
dimension $8$ and at radius $2$ in dimension $24$.

## Sources

- H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, and M. Viazovska, 'Universal optimality of the E8 and Leech lattices and interpolation formulas', Ann. of Math. 196 (2022), 983-1082, Theorem 1.9, https://doi.org/10.4007/annals.2022.196.3.3. Via leanprover/lean-eval@38361be, problem `ckmrv_fourier_interpolation`.
