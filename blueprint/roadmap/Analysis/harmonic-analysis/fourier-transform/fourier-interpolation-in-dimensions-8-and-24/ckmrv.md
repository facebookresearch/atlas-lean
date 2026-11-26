# Radial Fourier interpolation property

Let $n \ge 1$ and $k_0 \ge 0$ be integers. For a
complex-valued Schwartz function $f$ on $\mathbb{R}^n$, let
$\hat f(\xi) = \int f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ be its Fourier transform, let
$e_1$ be the first standard basis vector and let $r_k = \sqrt{2k}$. The sampling map from index
$k_0$ sends $f$ to the four complex sequences indexed by the integers $k \ge k_0$ whose $k$-th
terms are $f(r_k e_1)$, $\hat f(r_k e_1)$ and the derivatives at $r = r_k$ of
$r \mapsto f(r e_1)$ and of $r \mapsto \hat f(r e_1)$. Call $f$ radial if $f(x) = f(y)$ whenever
$|x| = |y|$, and call a sequence $(a_k)_{k \ge k_0}$ rapidly decreasing if $k^m |a_k| \to 0$ as
$k \to \infty$ for every natural number $m$. The property $\mathrm{CKMRV}(n, k_0)$ holds when
the sampling map from index $k_0$ is a bijection from the radial Schwartz functions on
$\mathbb{R}^n$ onto the quadruples of rapidly decreasing sequences indexed by $k \ge k_0$.

The bijection is required to be the sampling map itself, so no interpolation basis is hidden
in the definition.
