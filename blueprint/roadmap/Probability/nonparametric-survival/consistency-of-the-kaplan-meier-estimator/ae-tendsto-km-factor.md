# Convergence of the Kaplan–Meier factors

Let $Z_i = (T_i, C_i)$ be independent, each with the law of the independent censoring model: the
product of a law of $T$ and a law of $C$ on the grid $\{0, 1, \dots, k - 1\}$. Almost surely,
simultaneously for every grid point $j$ with $\Pr[\min(T, C) \ge j] \ne 0$, the Kaplan–Meier factor
$1 - d_j(n) / Y_j(n)$ of the empirical data of the first $n$ subjects converges to $1 - h(j)$ as
$n \to \infty$, where $h$ is the discrete hazard of $T$. At a sample size where none of the first $n$
subjects is at risk at $j$, $Y_j(n) = d_j(n) = 0$ and the factor is $1$.
