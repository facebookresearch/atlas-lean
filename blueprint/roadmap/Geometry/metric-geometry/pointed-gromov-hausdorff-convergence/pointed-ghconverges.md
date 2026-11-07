# Pointed Gromov–Hausdorff convergence

Let $X_0, X_1, \dots$ and $Y$ be pseudometric
spaces with base points $p_n \in X_n$ and $q \in Y$. The sequence $(X_n, p_n)$ converges to
$(Y, q)$ in the pointed Gromov–Hausdorff sense if for all $R > 0$ and $\varepsilon > 0$ there is
$N$ such that for every $n \ge N$ there is a map $f$ from the open ball $B(p_n, R)$ to $Y$ with
$f(p_n) = q$, with $|d(f(x), f(y)) - d(x, y)| \le \varepsilon$ for all $x, y \in B(p_n, R)$, and
such that every point of the open ball $B(q, R - \varepsilon)$ is at distance less than
$\varepsilon$ from some point of the image of $f$.

No measurability or continuity is required of $f$, and the spaces need not be complete or
separable, so this extends the metric part of the pointed measured Gromov–Hausdorff convergence
of Gigli–Mondino–Savaré, who use Borel maps on complete separable spaces. Open balls are an
implementation choice for their unspecified balls $B_R$.
