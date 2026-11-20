# Discrete product-limit identity

For a law of $T$ on the grid $\{0, 1, \dots, k - 1\}$ and an index $m$ with $\Pr[T \ge m] \ne 0$,
$$\prod_{j \le m} (1 - h(j)) = \Pr[T > m],$$
where $h(j) = \Pr[T = j] / \Pr[T \ge j]$ is the discrete hazard. The factors telescope:
$1 - h(j) = \Pr[T > j] / \Pr[T \ge j]$ and $\Pr[T \ge j + 1] = \Pr[T > j]$, starting from
$\Pr[T \ge 0] = 1$.
