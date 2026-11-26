# The short integer solution problem (SIS)

Let $n, m, q, \beta$ be positive integers. For $A \in \mathbb{Z}_q^{n \times m}$, a *short integer solution* is a nonzero vector $z \in \mathbb{Z}^m$ with $\|z\|_\infty \le \beta$ and $A z \equiv 0 \pmod q$; equivalently, a nonzero vector of norm at most $\beta$ in the $q$-ary kernel lattice

$$
\Lambda_q^{\perp}(A) = \{ z \in \mathbb{Z}^m : A z \equiv 0 \pmod q \}.
$$

The problem $\mathrm{SIS}_{n,m,q,\beta}$ asks, given a uniformly random $A \in \mathbb{Z}_q^{n \times m}$, to output such a $z$. For a parameter family $(n(\kappa), m(\kappa), q(\kappa), \beta(\kappa))$ with $q(\kappa) \ne 0$, the *SIS assumption* states that every probabilistic polynomial-time algorithm, given $1^\kappa$ and a uniform $A$, outputs a short integer solution with probability negligible in $\kappa$. (When $\beta \ge q$ the vector $q e_1$ is always a solution, so the assumption is only meaningful for $\beta < q$.)

## Depends on

- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)
- [Winning probability of a game](../../../security-games/games-and-advantages/win-prob.md)

## Sources

- Miklós Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing (STOC '96), 1996.
- Daniele Micciancio and Oded Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing, 2007.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
