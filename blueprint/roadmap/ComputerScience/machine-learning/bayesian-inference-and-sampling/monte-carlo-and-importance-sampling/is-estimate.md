# Importance-sampling estimate

Given a weight $w : \alpha \to [0, \infty]$, a function
$f : \alpha \to \mathbb{R}$ and samples $X_0, X_1, \ldots : \Omega \to \alpha$, the
importance-sampling estimate from the first $n$ samples at $\omega \in \Omega$ is
$\frac{1}{n} \sum_{i < n} w(X_i(\omega)) \, f(X_i(\omega))$, where an infinite weight counts as
$0$ and the estimate is $0$ when $n = 0$. If the samples are drawn from a proposal measure
$\rho$, it estimates $\int f \, d\nu$ for the target measure $\nu$ with density $w$ with respect to
$\rho$.
