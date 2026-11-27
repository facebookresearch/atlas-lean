# Foster's recurrence criterion

Let $X$ be an irreducible [Markov chain](../construction-of-markov-chains/markov-chain-construction.md) on a countable state space $S$ with transition matrix $P$, and write $Pf(x) = \sum_y P(x, y) f(y)$. Suppose there are a finite set $F \subset S$ and a function $f : S \to [0, \infty)$ such that

1. $Pf(x) \le f(x)$ for all $x \notin F$, and
2. $\{x \in S : f(x) \le M\}$ is finite for every $M > 0$.

Then $X$ is recurrent.

**Proof idea.** If from some state the chain stays forever in a finite set with positive probability, some state of that set is visited infinitely often with positive probability, so it is recurrent, and the chain is recurrent by irreducibility. Otherwise the exit time $S_M$ of every finite level set $\{f \le M\}$ is almost surely finite. Stopped at the hitting time $D$ of $F$, $f(X_{n \wedge D})$ is a nonnegative supermartingale, and optional stopping, applied to the bounded times $n \wedge D \wedge S_M$ and then letting $n \to \infty$, gives $f(x) \ge M\,P_x[S_M < D]$. Since $D = \infty$ forces $S_M < D$, $P_x[D = \infty] \le f(x)/M$ for every $M$, so $F$ is reached almost surely from every state, hence visited infinitely often, and one of its finitely many states is recurrent.

## Depends on

- [Markov chain construction](../construction-of-markov-chains/markov-chain-construction.md)

## Proof depends on

- [Optional stopping for supermartingales](../../martingales/optional-stopping-theorem/expected-stopped-value-anti-mono.md): applied to the bounded stopping times $n \wedge D \wedge S_M$.

## Sources

- P. J. Fitzsimmons, *Foster–Liapunov criterion*, lecture notes, Math 280C, University of California San Diego, 2012, <https://mathweb.ucsd.edu/~pfitz/downloads/courses/spring12/math280c/foster.pdf>, Proposition and Theorem 1 with their proofs.
- F. G. Foster, "On the stochastic matrices associated with certain queuing processes", *Annals of Mathematical Statistics* 24:355–360, 1953, cited there as the origin of the criterion.
