# Sifting by a set with reciprocal sum at most one leaves many integers

The sieve bound holds at every level $0 < C \le 1$, where for a real $C$, the sieve bound at level $C$ holds when there are $c > 0$ and $\kappa > 0$ such that for all sufficiently large $x$ and every $A \subseteq \{2, \dots, x\}$ with $\sum_{a \in A} 1/a \le C$, at least $\kappa x/(\log x)^c$ integers $m \in \{1, \dots, x\}$ are divisible by no element of $A$.

Problem 784 as printed takes $A \subseteq [1, x]$; then $A = \{1\}$ leaves no integer, so the problem intends $1 \notin A$, and the statement here takes $A \subseteq \{2, \dots, x\}$.

This resolves [Erdős Problem 784 for reciprocal sums at most one](sieve-lower-bound-small-reciprocal-sum.md), the statement recorded as a proposition, in the affirmative: Ruzsa (1982) proved the lower bound $H_1(x) \ge x/(10 \log x)$ for the least number of survivors at level $1$, and $H_C \ge H_1$ for $0 < C \le 1$. Weingartner (2025) gives sharper estimates.

## Sources

- T. F. Bloom, Erdős Problems, Problem #784, https://www.erdosproblems.com/784.
- I. Z. Ruzsa, On the small sieve. II. Sifting by composite numbers, J. Number Theory (1982), 260–268.
- A. Weingartner, The Schinzel–Szekeres function, Res. Number Theory (2025), Paper No. 63.
