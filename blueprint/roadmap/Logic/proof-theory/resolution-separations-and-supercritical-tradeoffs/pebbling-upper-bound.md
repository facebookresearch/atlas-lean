# Pebbling formulas have linear-size resolution refutations

Let $G$ be a DAG with $n$ vertices and a unique sink in which every vertex has in-degree at most $2$. The pebbling formula $\mathrm{Peb}_G$ has a resolution refutation of size $O(n)$ and width at most $3$, and for every non-constant Boolean function $f$ of arity $\ell$ the substituted formula $\mathrm{Peb}_G[f]$ has a resolution refutation of size $2^{O(\ell)}\, n$ and width $O(\ell)$.

## Proof sketch

Derive the unit clauses $x_v$ in a topological order of $G$: sources are axioms, and from the units $x_u$ for $u \in \mathrm{pred}(v)$ and the clause $\bigvee_{u \in \mathrm{pred}(v)} \neg x_u \vee x_v$ at most two resolution steps give $x_v$; finally resolve $x_z$ with $\neg x_z$. For $\mathrm{Peb}_G[f]$, derive in the same order the canonical CNF of $f(x_{v,1}, \dots, x_{v,\ell})$. Each of its at most $2^{\ell}$ clauses is implied by the already derived CNFs of the predecessors together with the substituted clause for $v$, all over at most $3\ell$ variables, so it has a derivation of size $2^{O(\ell)}$ within those variables; at the sink the CNFs of $f(x_{z,\cdot})$ and $\neg f(x_{z,\cdot})$ are refuted in size $2^{O(\ell)}$.

## Depends on

- [Pebbling formulas of directed acyclic graphs](pebbling-formula.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013).
