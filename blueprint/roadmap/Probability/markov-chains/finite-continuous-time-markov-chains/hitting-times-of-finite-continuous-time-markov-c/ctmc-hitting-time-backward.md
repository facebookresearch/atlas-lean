# Backward equations for the mean hitting time

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a finite set $S$, with exit rates $q(i) = -Q(i, i)$ and [jump matrix](../finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md) $\Pi$. Write $\mathbb E_i$ for the expectation, under the [law of the step sequence](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md), of a functional of the chain started at $i$, and $H_A$ for the [hitting time](ctmc-hitting-time.md) of $A \subseteq S$, valued in $[0, \infty]$. Let $A \subseteq S$ and let $m : S \to \mathbb{R}$ satisfy $m(i) \ge 0$ for every $i$ and
$(Qm)(i) = -1$ for every $i \notin A$. Then

1. $\mathbb E_i H_A \le m(i)$ for every $i \in S$; in particular $\mathbb E_i H_A < \infty$;
2. $\mathbb E_i H_A = 0$ for $i \in A$;
3. the real vector $h(j) = \mathbb E_j H_A$ satisfies $(Qh)(i) = -1$ for every $i \notin A$.

With uniqueness of the solution of these equations, this identifies $\mathbb E_i H_A$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 3.3 (compare).
