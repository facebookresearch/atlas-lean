# Conditional on acceptance, the proposal has the target law

Let $p$ and $q$ be probability
mass functions on $\alpha$ and $M \in [0, \infty]$ with $M \ne 0$, $M \ne \infty$ and
$p(y) \le M\,q(y)$ for all $y \in \alpha$. For one round of rejection sampling for target $p$,
proposal $q$ and envelope $M$, write $P(x, \mathrm{accepted})$ for the probability that the round
proposes $x$ and accepts it, and
$P(\mathrm{accepted}) = \sum_{y \in \alpha} P(y, \mathrm{accepted})$. Then
$P(x, \mathrm{accepted}) / P(\mathrm{accepted}) = p(x)$ for every $x \in \alpha$.
