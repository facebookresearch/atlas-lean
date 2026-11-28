# The totient pattern-length ratio has no positive limit

It is not the case that there is a real $c > 0$ with $F(n)/\log\log\log n \to c$ as $n \to \infty$, where $F(n)$ is the largest $k \le n$ such that every permutation of $\{0, \dots, k-1\}$ appears among $k$ consecutive totient values $\varphi(m+1), \dots, \varphi(m+k)$ with $m + k \le n$, a permutation $\sigma$ appearing in $x_0, \dots, x_{k-1}$ when $\sigma(i) < \sigma(j)$ implies $x_i < x_j$.

This refutes [Erdős Problem 415 (patterns in consecutive values of the totient function)](conjecture.md), the statement recorded as a proposition; the refutation is due to Pollack, Pomerance and Treviño (2013), cited under Sources, whose bound on monotone runs of totient values, with $F(n) \le G(n)$ for the longest monotone run $G(n)$, gives the stronger estimate that this ratio tends to $0$; the statement here asserts only that it has no positive limit.

## Sources

- T. F. Bloom, Erdős Problems, Problem #415, https://www.erdosproblems.com/415.
- P. Pollack, C. Pomerance and E. Treviño, Sets of monotonicity for Euler's totient function, Ramanujan J. 30 (2013), 379–398, https://doi.org/10.1007/s11139-012-9386-6.
