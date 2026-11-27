# Lagarias' elementary criterion for the Riemann hypothesis

The Riemann hypothesis holds
(every zero $s$ of the Riemann zeta function with $s \ne 1$ that is not one of the trivial zeros
$-2, -4, -6, \dots$ has real part $1/2$) if and only if, for every positive integer $n$,

$$\sigma(n) \le H_n + e^{H_n} \log H_n,$$

where $\sigma(n)$ is the sum of the positive divisors of $n$ and $H_n = \sum_{k=1}^{n} 1/k$ is
the $n$-th harmonic number.

## Sources

- https://arxiv.org/abs/math/0008177. Problem `riemann_hypothesis_iff_lagarias_elementary_criterion` of the lean-eval benchmark.
