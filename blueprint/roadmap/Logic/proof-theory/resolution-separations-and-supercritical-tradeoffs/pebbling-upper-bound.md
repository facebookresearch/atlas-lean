# Pebbling formulas have linear-size resolution refutations

For every DAG $G$ with $n$ vertices of in-degree at most $2$, the pebbling formula $\mathrm{Peb}_G$ has a resolution refutation of size $O(n)$ and width $3$, and $\mathrm{Peb}_G[\oplus_\ell]$ has a resolution refutation of size $O(2^{3\ell} n)$ for every constant $\ell$.

## Proof sketch

Derive the unit clauses $x_v$ in a topological order of $G$: sources are axioms, and from $x_u$, $x_w$ and $\neg x_u \vee \neg x_w \vee x_v$ two resolution steps give $x_v$; finally resolve $x_z$ with $\neg x_z$. For substituted formulas, derive the CNF encoding of $\oplus_\ell(x_{v,\cdot})$ in the same order, each step costing $2^{O(\ell)}$ clauses.

## Depends on

- [Pebbling formulas of directed acyclic graphs](pebbling-formula.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013).
