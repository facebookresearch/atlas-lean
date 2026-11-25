# Rejection sampling outputs the posterior law

Let a Bayesian network have finitely many variables with values in a finite nonempty set, let $e$ be evidence on a set $E$ of variables with probability $P(E = e) \ne 0$, and let $x$ be a full assignment. In repeated independent forward samples, summing over the number $k$ of rejected samples the probability that the first sample consistent with the evidence is exactly $x$,

$$\sum_{k \ge 0} \big(1 - P(E = e)\big)^k \, P(x)\,\mathbf 1[x_E = e] = P(x \mid E = e).$$
