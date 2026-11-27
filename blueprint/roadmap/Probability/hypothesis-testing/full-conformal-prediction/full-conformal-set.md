# Full conformal prediction set

Let $z = (z_1, \dots, z_n)$ be $n$ data points $z_i = (x_i, y_i) \in \mathcal X \times \mathcal Y$,
let $x$ be a test covariate, and let $S$ be a score map on augmented data vectors of length
$n + 1$. For a trial response $y$, write $R^y = S(z_1, \dots, z_n, (x, y))$. The full conformal set
at level $k$ is

$$C_k(z, x) = \bigl\{ y \in \mathcal Y : R^y_{n+1} \le R^y_{(k)} \bigr\},$$

where $R^y_{(k)}$ is the $k$-th smallest of $R^y_1, \dots, R^y_n$, counted with multiplicity,
$+\infty$ when $k > n$, and for $k = 0$ the smallest of them ($+\infty$ if $n = 0$). For $k \ge 1$,
equivalently, $y$ is kept when fewer than $k$ of the $n$ data scores are strictly smaller than the
trial score. The level used in the theorems is
$k = \lceil (1 - \alpha)(n + 1) \rceil$.

When the $n + 1$ scores are distinct, this is the set $\{y : (n + 1)\pi(y) \le \lceil (1 - \alpha)(n + 1) \rceil\}$
of Lei et al., equation (7). The two sets treat ties differently. Their $\pi(y)$ in (5) counts the
data scores with $R^y_i \le R^y_{n+1}$, so a trial value tied with many data scores is excluded.
In the set above only the strictly smaller scores count, as in the [split conformal threshold](../split-conformal-prediction/split-conformal-threshold.md),
so such a value is kept. With the count of (5), the lower coverage bound needs the scores to be
almost surely distinct (or ties to be broken at random). For example, if every residual is $0$
almost surely, the set (7) never contains $Y_{n+1}$ once $\alpha \ge 1/(n+1)$. With the count of the set above,
the lower bound holds with no assumption on ties.

## Background

- [Split conformal threshold](../split-conformal-prediction/split-conformal-threshold.md): the $k$-th smallest calibration score, applied to the augmented scores.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Equations (4), (5) and (7) and Algorithm 1.
