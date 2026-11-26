# Sifting by a set with reciprocal sum above one can leave few integers

It is not the case that the sieve bound holds at some level $C > 1$, where for a real $C$, the sieve bound at level $C$ holds when there are $c > 0$ and $\kappa > 0$ such that for all sufficiently large $x$ and every $A \subseteq \{2, \dots, x\}$ with $\sum_{a \in A} 1/a \le C$, at least $\kappa x/(\log x)^c$ integers $m \in \{1, \dots, x\}$ are divisible by no element of $A$.

Problem 784 as printed takes $A \subseteq [1, x]$; then $A = \{1\}$ leaves no integer, so the problem intends $1 \notin A$, and the statement here takes $A \subseteq \{2, \dots, x\}$.

This refutes [Erdős Problem 784 for reciprocal sums above one](sieve-lower-bound-large-reciprocal-sum.md), the statement recorded as a proposition; the refutation is due to Ruzsa (1982), who showed that for fixed $C > 1$ the least number of survivors is $x^{e^{1-C} + o(1)}$, below $\kappa x/(\log x)^c$ for every $c, \kappa > 0$; Weingartner (2025) sharpened this to $\asymp x^{e^{1-C}}/\log x$. Both are cited under Sources.

## Sources

- T. F. Bloom, Erdős Problems, Problem #784, https://www.erdosproblems.com/784.
- I. Z. Ruzsa, On the small sieve. II. Sifting by composite numbers, J. Number Theory (1982), 260–268.
- A. Weingartner, The Schinzel–Szekeres function, Res. Number Theory (2025), Paper No. 63.
