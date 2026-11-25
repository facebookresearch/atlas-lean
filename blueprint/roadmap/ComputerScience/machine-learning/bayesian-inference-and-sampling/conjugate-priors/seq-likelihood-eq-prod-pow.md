# The sequence likelihood depends only on the label counts

For every
$\theta \in \mathbb{R}^{n+1}$ and every sequence $s$ of $N$ labels in $\{0, \dots, n\}$ with
label counts $n_i(s)$, the likelihood $\prod_{m < N} \theta_{s_m}^+$ of $s$ equals
$\prod_{i = 0}^{n} (\theta_i^+)^{n_i(s)}$ as extended nonnegative reals, where
$x^+ = \max(x, 0)$.
