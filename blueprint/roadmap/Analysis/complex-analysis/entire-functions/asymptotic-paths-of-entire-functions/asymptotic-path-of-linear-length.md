# Erdős Problem 1115 on asymptotic paths of linear length

Erdős Problem 1115, the question "can such a path be found with $\ell(r) \ll r$": every nonconstant entire function $f$ of [finite order](has-finite-order.md) tends to $\infty$ along a locally rectifiable path to $\infty$ whose length inside $|z| < r$ is $O(r)$.

Paths are parametrized by arc length, so the statement reads: there are a $1$-Lipschitz map $\gamma : \mathbb{R} \to \mathbb{C}$ with $|f(\gamma(t))| \to \infty$ as $t \to \infty$, and a constant $C$, such that for every $r \ge 1$

$$
\operatorname{vol}\{t \ge 0 : |\gamma(t)| < r\} \le C r,
$$

where $\operatorname{vol}$ is Lebesgue measure on $\mathbb{R}$. For a $1$-Lipschitz $\gamma$ the length $\ell(r)$ of $\gamma|_{[0, \infty)}$ inside $|z| < r$ is at most this measure, with equality for unit speed, so the bound holds for some such $\gamma$ exactly when some path has $\ell(r) \ll r$.

Its resolution: [Entire functions of finite order without asymptotic paths of linear length](asymptotic-path-of-linear-length-refuted.md).
