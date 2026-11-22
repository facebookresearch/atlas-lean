# Robin's inequality for every $n > 5040$

For every natural number $n > 5040$,

$$
\sigma(n) < e^{\gamma} \, n \log \log n,
$$

where $\sigma(n)$ is the sum of the positive divisors of $n$, $\gamma$ is the Euler–Mascheroni
constant, and $\log$ is the natural logarithm.

This is the Riemann hypothesis read through Robin's criterion, which states that the Riemann
hypothesis holds if and only if the inequality holds for every $n > 5040$.

## Proof depends on

- [Riemann hypothesis](../zeros-of-the-riemann-zeta-function/riemann-hypothesis.md)
- [Robin's criterion for the Riemann hypothesis](robin-criterion-for-riemann-hypothesis.md)

## Sources

- Sadegh Nazardonyavi and Semyon Yakubovich, "Extremely Abundant Numbers and the Riemann Hypothesis", Journal of Integer Sequences 17 (2014), Article 14.2.8, abstract, lines 77–80, for Robin's criterion, attributed there to Robin, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex>.
- A. Sutherland, *Verification files for the Lean proof of the Riemann Hypothesis*, <https://math.mit.edu/~drew/grh/>, section "Arithmetic consequences": combining the library with an independent formalization of Robin's and Lagarias's criteria (kimihiro64/Robin1984, commit `acab1a3`) gives `robin_inequality` and `lagarias_inequality` in Lean, with no hypotheses.
- Proof of the Riemann hypothesis: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
