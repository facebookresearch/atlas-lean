# Ben-Sasson–Impagliazzo–Wigderson: near-optimal separation of tree-like and general resolution

Let $G_n$ be the DAGs of Paul, Tarjan and Celoni: $n$ vertices, a unique sink, in-degree at most $2$, and black pebbling price $\Omega(n/\log n)$. The OR-substituted pebbling formulas $F_n = \mathrm{Peb}_{G_n}[\vee_2]$, in which each variable $x_v$ is replaced by the two-input disjunction $x_{v,1} \vee x_{v,2}$, are unsatisfiable $4$-CNF formulas with $N = 2n$ variables and $O(n)$ clauses. They have general resolution refutations of size $O(n)$, but every tree-like resolution refutation of $F_n$ has size

$$
2^{\Omega(n/\log n)}.
$$

Since every unsatisfiable formula on $N$ variables has a tree-like refutation of size at most $2^{N+1}$, the separation is optimal up to the logarithmic factor in the exponent. The substitution is essential: the unsubstituted formula $\mathrm{Peb}_{G_n}$ (the identity substitution) has tree-like refutations of linear size, by input resolution backwards from the sink axiom.

## Proof sketch

For OR-substituted pebbling formulas, tree-like refutation size is at least $2^{\Omega(\text{black pebbling price of } G)}$, via a Prover-Delayer game whose Delayer strategy relies on the OR substitution (fixing one variable of a pair to $0$ leaves the value of $x_{v,1} \vee x_{v,2}$ open), so that the Prover is forced to follow a pebbling strategy. The graphs $G_n$ have pebbling price $\Omega(n/\log n)$, while the general refutation is linear by the upper bound for substituted pebbling formulas.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Pebbling formulas of directed acyclic graphs](pebbling-formula.md)

## Proof depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013) (Definitions 2.11 and 2.12, Section 3.2).
