# Transition matrix of the systematic-scan Gibbs sweep

Let $\pi$ be a probability distribution on the configurations $x : \iota \to S$, with $\iota$ and
$S$ finite, such that $\pi(x) \ne 0$ for every $x$, and let $l$ be a list of coordinates. The
transition matrix of the systematic-scan Gibbs sweep along $l$ is the real matrix indexed by
configurations with entries $P(x, y) = K_l(x)(\{y\})$, where $K_l$ is the
[systematic-scan Gibbs sampler](gibbs-sweep.md) along $l$.
