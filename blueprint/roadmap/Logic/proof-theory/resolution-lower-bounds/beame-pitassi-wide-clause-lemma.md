# Beame–Pitassi: refutations of the pigeonhole principle contain wide monotone clauses

For every $n \ge 2$, every resolution refutation of $\mathrm{PHP}^{n}_{n-1}$ ($n$ pigeons, $n - 1$ holes) contains a clause whose monotonization has at least $2n^2/9$ literals. Combined with a greedy choice of one pigeon–hole pair at a time (restricting $p_{i,j} = 1$ and the rest of row $i$ and column $j$ to $0$), which shrinks the instance by one pigeon and one hole and, at each step, satisfies at least a tenth of the clauses with at least $n^2/10$ literals, this shows that for sufficiently large $n$ every resolution refutation of $\mathrm{PHP}^{n}_{n-1}$ has at least $2^{n/20}$ clauses.

## Proof sketch

Following the refutation backwards from the empty clause along clauses falsified by critical assignments, consider the first clause whose falsifying critical assignments omit between $n/3$ and $2n/3$ pigeons; an exchange argument on critical assignments shows its monotonization contains many variables. Each restriction step preserves the pigeonhole structure on the remaining pigeons and holes.

## Depends on

- [Critical truth assignments for the pigeonhole principle](critical-truth-assignments.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Restrictions of resolution refutations](restrictions-of-resolution-refutations.md)

## Sources

- P. Beame and T. Pitassi, "Simplified and Improved Resolution Lower Bounds", Proceedings of the 37th IEEE Symposium on Foundations of Computer Science (FOCS), 1996: Section 3, Lemma 1 and Theorem 2.
- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 297–308, 1985.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
