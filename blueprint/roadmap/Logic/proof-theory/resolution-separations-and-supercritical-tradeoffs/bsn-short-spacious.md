# Ben-Sasson–Nordström: short resolution proofs may require large space

The **clause space** of a resolution refutation is the maximum number of clauses that must be kept in memory simultaneously when the refutation is presented as a sequence of configurations. There are explicit families of $O(1)$-CNF formulas $F_n$ of size $\Theta(n)$ that have resolution refutations of size $O(n)$ and width $O(1)$ but every resolution refutation of $F_n$ requires clause space $\Omega(n/\log n)$. This is optimal, since every formula of size $n$ has refutations in clause space $O(n)$, and it separates space from both length and width.

## Proof sketch

Use XOR-substituted pebbling formulas of DAGs with black-white pebbling price $\Omega(n/\log n)$. Linear-size refutations follow the pebbling order. For the space lower bound, show that any memory configuration of small clause space, projected onto the substituted variables, corresponds to a black-white pebble configuration of comparable size, so a small-space refutation would give a cheap pebbling strategy.

## Depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Proof depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Sources

- E. Ben-Sasson, J. Nordström, "Short proofs may be spacious: an optimal separation of space and length in resolution", FOCS (2008).
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013).
