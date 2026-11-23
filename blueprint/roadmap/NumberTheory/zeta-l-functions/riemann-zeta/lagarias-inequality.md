# Lagarias' inequality for every positive integer

For every positive integer $n$,

$$
\sigma(n) \le H_n + e^{H_n} \log H_n,
$$

where $\sigma(n)$ is the sum of the positive divisors of $n$ and $H_n = \sum_{k=1}^{n} 1/k$ is the
$n$-th harmonic number.

This is the Riemann hypothesis read through Lagarias' elementary criterion, which states that the
Riemann hypothesis holds if and only if the inequality holds for every positive integer $n$.

## Proof depends on

- [Riemann hypothesis](zeros-of-the-riemann-zeta-function/riemann-hypothesis.md)
- [Lagarias' elementary criterion for the Riemann hypothesis](riemann-hypothesis-iff-lagarias-elementa.md)

## Sources

- J. C. Lagarias, *An elementary problem equivalent to the Riemann hypothesis*, Amer. Math. Monthly 109 (2002), 534–543, arXiv:math/0008177, for the criterion.
- A. Sutherland, *Verification files for the Lean proof of the Riemann Hypothesis*, <https://math.mit.edu/~drew/grh/>, section "Arithmetic consequences": combining the library with an independent formalization of Robin's and Lagarias's criteria (kimihiro64/Robin1984, commit `acab1a3`) gives `robin_inequality` and `lagarias_inequality` in Lean, with no hypotheses.
- Proof of the Riemann hypothesis: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
