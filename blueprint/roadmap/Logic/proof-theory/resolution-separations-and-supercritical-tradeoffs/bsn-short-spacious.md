# Ben-Sasson–Nordström: short resolution proofs may require large space

The **clause space** of a resolution refutation is the maximum number of clauses that must be kept in memory simultaneously when the refutation is presented as a sequence of configurations. There are explicitly constructible families of $6$-CNF formulas $F_n$ of size $O(n)$ that have resolution refutations of length $O(n)$ and width $O(1)$, but every resolution refutation of $F_n$ requires clause space $\Omega(n/\log n)$. This is asymptotically optimal: every formula with a resolution refutation of length $L$ has one in clause space $O(L/\log L)$, which is $O(n/\log n)$ here. The result separates space from both length and width.

## Proof sketch

Use XOR-pebbling formulas $\mathrm{Peb}_G[\oplus_2]$, with two variables per vertex, over fan-in-$2$ DAGs $G$ with a unique sink, $O(n)$ vertices and black-white pebbling price $\Omega(n/\log n)$ (Gilbert–Tarjan). Linear-length, constant-width refutations follow the pebbling order. For the space lower bound, show that the clause space of refuting $\mathrm{Peb}_G[\oplus_d]$, $d \ge 2$, is at least the black-white pebbling price of $G$ minus a constant: any memory configuration, projected onto the vertices of $G$, corresponds to a resolution-pebbling configuration whose cost is bounded by the number of clauses, so a small-space refutation would give a cheap black-white pebbling strategy.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Sources

- E. Ben-Sasson, J. Nordström, "Short proofs may be spacious: an optimal separation of space and length in resolution", FOCS (2008) (Theorem 1.1, Corollary 1.2).
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013).
