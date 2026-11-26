# Pebbling formulas of directed acyclic graphs

Let $G$ be a directed acyclic graph with a unique sink $z$, in which every non-source vertex has in-degree $2$. The **pebbling formula** $\mathrm{Peb}_G$ has one variable $x_v$ per vertex and the clauses: $x_s$ for every source $s$; $\neg x_u \vee \neg x_w \vee x_v$ for every vertex $v$ with predecessors $u, w$; and $\neg x_z$. For an integer $\ell$ and a Boolean function $\oplus_\ell$ of arity $\ell$ (typically XOR), the **substituted pebbling formula** $\mathrm{Peb}_G[\oplus_\ell]$ replaces each $x_v$ by $\oplus_\ell(x_{v,1}, \dots, x_{v,\ell})$ and expands into CNF.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013).
