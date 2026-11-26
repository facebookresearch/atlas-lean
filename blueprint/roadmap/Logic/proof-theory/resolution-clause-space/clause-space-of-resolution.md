# Clause space of resolution refutations

A *configuration-style resolution refutation* of a CNF formula $\varphi$ is a sequence of sets of clauses (memory configurations) $\mathbb{M}_0 = \emptyset, \mathbb{M}_1, \dots, \mathbb{M}_\tau$ in which each step either downloads a clause of $\varphi$, adds the resolvent of two clauses currently in memory, or erases a clause, and $\mathbb{M}_\tau$ contains the empty clause. Its *clause space* is $\max_t |\mathbb{M}_t|$. The clause space $\mathrm{Sp}(\varphi \vdash \bot)$ of an unsatisfiable formula is the minimum clause space of a refutation. Every unsatisfiable formula on $N$ variables is refutable in clause space $N + 2$.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Resolvent of two clauses](../../propositional-logic/resolution/resolvent.md)

## Sources

- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001.
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
- Y. Filmus, M. Lauria, M. Mikša, J. Nordström and M. Vinyals, "From Small Space to Small Width in Resolution", 31st Symposium on Theoretical Aspects of Computer Science (STACS), 2014.
