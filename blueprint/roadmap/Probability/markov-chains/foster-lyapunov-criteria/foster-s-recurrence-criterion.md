# Foster's recurrence criterion

Let $X$ be an irreducible [Markov chain](../construction-of-markov-chains/markov-chain-construction.md) on a countable state space $S$ with transition matrix $P$, and write $Pf(x) = \sum_y P(x, y) f(y)$. Suppose there are a finite set $F \subset S$ and a function $f : S \to [0, \infty)$ such that

1. $Pf(x) \le f(x)$ for all $x \notin F$, and
2. $\{x \in S : f(x) \le M\}$ is finite for every $M > 0$.

Then $X$ is recurrent.

**Proof idea.** Stopped at the hitting time $D$ of $F$, $f(X_{n \wedge D})$ is a nonnegative supermartingale. If the chain left every level set $\{f \le M\}$ before reaching $F$ with probability bounded away from $0$, optional stopping at the exit time $S_M$ would give $f(x) \ge M\,P_x[S_M < D]$ for every $M$; hence $F$ is reached almost surely from every state, visited infinitely often, and one of its finitely many states is recurrent.

## Depends on

- [Markov chain construction](../construction-of-markov-chains/markov-chain-construction.md)

## Sources

- P. J. Fitzsimmons, *Foster–Liapunov criterion*, lecture notes, Math 280C, University of California San Diego, 2012, <https://mathweb.ucsd.edu/~pfitz/downloads/courses/spring12/math280c/foster.pdf>, Proposition and Theorem 1 with their proofs.
- F. G. Foster, "On the stochastic matrices associated with certain queuing processes", *Annals of Mathematical Statistics* 24:355–360, 1953, cited there as the origin of the criterion.
