# Learning with errors

Let $n, m, q$ be positive integers and $\chi$ a distribution on $\mathbb{Z}_q$. In the *search* learning-with-errors problem $\mathrm{LWE}_{n,m,q,\chi}$, given $(A, As + e)$ with $A$ uniform in $\mathbb{Z}_q^{m \times n}$, $s$ uniform in $\mathbb{Z}_q^n$ and $e \sim \chi^m$, the task is to find $s$. In the *decision* problem, the task is to distinguish $(A, As + e)$ from $(A, u)$ with $u$ uniform in $\mathbb{Z}_q^m$. For a family of parameters indexed by the dimension $n$, with $m$ and $q$ bounded by polynomials in $n$, the decision LWE assumption asserts that every algorithm running in time polynomial in $n$ has advantage negligible in $n$ in the decision problem.

## Depends on

- [Winning probability of a game](../../security-games/games-and-advantages/win-prob.md)

## Sources

- O. Regev, "On lattices, learning with errors, random linear codes, and cryptography", *Journal of the ACM* 56(6), Article 34, 2009, Sections 1 and 2; <https://arxiv.org/abs/2401.03703>
- C. Peikert, "A decade of lattice cryptography", *Foundations and Trends in Theoretical Computer Science* 10(4):283–424, 2016; ePrint 2015/939, <https://eprint.iacr.org/2015/939>
