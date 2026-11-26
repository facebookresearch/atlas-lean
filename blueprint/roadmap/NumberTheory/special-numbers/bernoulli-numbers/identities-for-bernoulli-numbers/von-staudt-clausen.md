# Von Staudt–Clausen theorem

For every integer $k \ge 0$, let $P_k$ be the set of primes $p \le 2k + 1$ such that $p - 1$ divides $2k$. Then the rational number $B_{2k} + \sum_{p \in P_k} 1/p$ is an integer, where $B_{2k}$ is a Bernoulli number. For $k \ge 1$, every prime $p$ with $p - 1 \mid 2k$ satisfies $p \le 2k + 1$, so the sum runs over all such primes. For $k = 0$, the set $P_0$ is empty and the statement asserts that $B_0$ is an integer, which holds since $B_0 = 1$.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the statement with the sum over primes below $2k + 2$: `Bernoulli.vonStaudt_clausen`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Bernoulli.lean#L666-L671.
