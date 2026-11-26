# The likelihood-weighting numerator is unbiased

In a Bayesian network over a nonempty alphabet with joint law $P$, fix evidence $x_E = e$ on a set $E$ of nodes and a function $f$. Let $X_1, X_2, \dots$ be measurable samples, each with the law of the network with $E$ clamped to $e$. Then for every $m \ge 1$, the likelihood-weighting estimate from the first $m$ samples has expectation $\sum_{x : x_E = e} P(x) f(x)$.
