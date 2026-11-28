# The short integer solution problem (SIS)

Let $n, m, q, \beta$ be positive integers. For $A \in \mathbb{Z}_q^{n \times m}$, a *short integer solution* is a nonzero vector $z \in \mathbb{Z}^m$ with $\|z\|_\infty \le \beta$ and $A z \equiv 0 \pmod q$; equivalently, a nonzero vector of $\ell_\infty$ norm at most $\beta$ in the $q$-ary kernel lattice

$$
\Lambda_q^{\perp}(A) = \{ z \in \mathbb{Z}^m : A z \equiv 0 \pmod q \}.
$$

The problem $\mathrm{SIS}_{n,m,q,\beta}$ asks, given a uniformly random $A \in \mathbb{Z}_q^{n \times m}$, to output such a $z$. For a parameter family $(n(\kappa), m(\kappa), q(\kappa), \beta(\kappa))$ with $q(\kappa) \ne 0$, the *SIS assumption* states that every probabilistic polynomial-time algorithm, given $1^\kappa$ and a uniform $A$, outputs a short integer solution with probability negligible in $\kappa$. (When $\beta \ge q$ the vector $q e_1$ is always a solution, so the assumption is only meaningful for $\beta < q$.) This is the $\ell_\infty$-norm variant of SIS (sometimes written $\ell_\infty$-SIS), which bounds every coordinate of the solution. Ajtai (Theorem 1), Micciancio and Regev (Definition 5.1) and Peikert (Definition 4.1.1) state SIS in the Euclidean norm, with a real bound and $\|z\|_2 \le \beta$; Micciancio and Peikert bound the $\ell_\infty$ norm of SIS solutions directly (2013, Theorem 1.1 and Theorem 3.8, where the $\ell_2$ bound $\sqrt m\,\beta$ adds no constraint). Since $\|z\|_\infty \le \|z\|_2 \le \sqrt m\,\|z\|_\infty$, a Euclidean solution with bound $\beta$ is an $\ell_\infty$ solution with bound $\beta$, and an $\ell_\infty$ solution with bound $\beta$ is a Euclidean solution with bound $\sqrt m\,\beta$.

## Depends on

- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)
- [Winning probability of a game](../../../security-games/games-and-advantages/win-prob.md)

## Sources

- Miklós Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing (STOC '96), 1996.
- Daniele Micciancio and Oded Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing, 2007.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
- Daniele Micciancio and Chris Peikert, "Hardness of SIS and LWE with Small Parameters", Advances in Cryptology (CRYPTO 2013), LNCS 8042, 2013.
