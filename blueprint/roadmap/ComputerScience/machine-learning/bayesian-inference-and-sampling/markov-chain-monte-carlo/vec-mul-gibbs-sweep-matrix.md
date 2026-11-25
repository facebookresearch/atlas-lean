# Target is stationary for the Gibbs sweep matrix

Let $\pi$ be a probability distribution on the configurations $x : \iota \to S$, with $\iota$ and
$S$ finite, such that $\pi(x) \ne 0$ for every $x$, and let $l$ be a list of coordinates. The
target is stationary for the [transition matrix](gibbs-sweep-matrix.md) $P$ of the
systematic-scan Gibbs sweep along $l$: $\sum_x \pi(x) P(x, y) = \pi(y)$ for every $y$.
