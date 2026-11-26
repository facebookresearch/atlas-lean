# Ben-Sasson–Impagliazzo–Wigderson: near-optimal separation of tree-like and general resolution

There is an explicit family of unsatisfiable $O(1)$-CNF formulas $F_n$ on $n$ variables (substituted pebbling formulas of graphs of high pebbling price) that have general resolution refutations of size $O(n)$ but every tree-like resolution refutation of $F_n$ has size

$$
2^{\Omega(n/\log n)}.
$$

Since every unsatisfiable formula on $n$ variables has a tree-like refutation of size at most $2^{n+1}$, the separation is optimal up to the logarithmic factor in the exponent.

## Proof sketch

Tree-like refutation size is at least $2^{\Omega(\text{black pebbling price})}$ for substituted pebbling formulas, via a Prover-Delayer game in which the Delayer exploits the substitution to force a pebbling strategy. Graphs with $n$ vertices and pebbling price $\Omega(n/\log n)$ exist (Paul-Tarjan-Celoni), while the general refutation is linear by the upper bound.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Pebbling formulas of directed acyclic graphs](pebbling-formula.md)

## Proof depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
