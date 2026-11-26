# Bounded-width implication (s-implication)

Let $\varphi$ be a CNF formula, $\tau$ a partial assignment and $s \ge 1$. A literal $x = b$ with $x$ unset in $\tau$ is **$s$-implied** by $(\varphi, \tau)$ if there is a set $\psi$ of at most $s$ clauses of $\varphi$ such that every total assignment that extends $\tau$ and satisfies all clauses of $\psi$ sets $x$ to $b$. The **$s$-implied value** of $x$ is $b$ if $x = b$ is $s$-implied and $x = 1 - b$ is not. For fixed $s$ and $k$ (the clause width), $s$-implication can be decided by exhaustive search over the at most $\sum_{j \le s}\binom{|\varphi|}{j}$ clause sets and the at most $k^s$ choices of one literal per chosen clause.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- R. Paturi, P. Pudlák, M. E. Saks and F. Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005.
- T. Hertli, "3-SAT Faster and Simpler: Unique-SAT Bounds for PPSZ Hold in General", 52nd IEEE Symposium on Foundations of Computer Science (FOCS), 2011.
