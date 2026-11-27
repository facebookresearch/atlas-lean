# Satisfiability coding lemma: PPZ round success probability

Let $\varphi$ be a satisfiable CNF formula on $n$ variables with clauses of at most $k \ge 1$ literals. One PPZ round succeeds with probability at least $2^{-(1 - 1/k)n}$.

## Proof sketch

For a satisfying assignment $\sigma$ that is isolated in direction $x$ (flipping $x$ falsifies $\varphi$), a critical clause for $x$ forces $x$ whenever $x$ comes last among its at most $k$ variables in $\pi$, which happens with probability at least $1/k$. Averaging over $\pi$, the expected number of guessed variables is at most $(1 - 1/k)n$ for isolated solutions; the general case follows by the satisfiability coding lemma's averaging over solutions.

## Depends on

- [Forced values and the PPZ round](ppz-forced-values-and-round.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", 38th IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
