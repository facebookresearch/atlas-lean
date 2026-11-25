# Relaxed triangle inequality for squared distance

For all points
$a, b, c \in \mathbb{Z}^d$, writing $\delta(x, y)$ for the squared distance from $x$ to $y$,
we have $\delta(a, c) \le 2\,(\delta(a, b) + \delta(b, c))$.

The factor $2$ comes from $(x + y)^2 \le 2(x^2 + y^2)$ applied coordinatewise. This is the
estimate that makes bounding-sphere pruning sound without square roots.
