# The chain of a Bayesian network

A Bayesian network $b$ on nodes $0, \dots, n - 1$ with
values in a nonempty type $\alpha$ defines a chain of conditional distributions. For $k < n$,
the conditional distribution of variable $k$ given values $y_0, \dots, y_{k-1}$ of the earlier
variables is the table of node $k$ applied to the values $y_j$ of its parents $j$. For
$k \ge n$ it is the point mass at a fixed arbitrary element of $\alpha$.
