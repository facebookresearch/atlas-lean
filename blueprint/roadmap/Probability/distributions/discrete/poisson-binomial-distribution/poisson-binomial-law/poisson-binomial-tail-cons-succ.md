# Poisson-binomial tail after adding a trial

Let $a \in \mathbb{R}$, $q \in \mathbb{R}^m$, and let $(a, q) \in \mathbb{R}^{m+1}$ be the vector with first entry
$a$ followed by $q$. For every $k \in \mathbb{N}$,

$$T_{k+1}(a, q) = T_{k+1}(q) + a\, \pi_q(k),$$

where $T$ is the [Poisson-binomial upper tail](poisson-binomial-tail.md) and $\pi$ the
[Poisson-binomial mass function](poisson-binomial-pmf.md). So the tail is affine in each trial's
probability, with slope a point mass of the remaining trials.
