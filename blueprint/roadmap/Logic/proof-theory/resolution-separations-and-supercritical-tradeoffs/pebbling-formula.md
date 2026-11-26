# Pebbling formulas of directed acyclic graphs

Let $G$ be a directed acyclic graph with a unique sink $z$ in which every vertex has in-degree at most $2$. The **pebbling formula** $\mathrm{Peb}_G$ has one variable $x_v$ per vertex and the following clauses:

- the unit clause $x_s$ for every source $s$;
- for every non-source $v$ with set of immediate predecessors $\mathrm{pred}(v)$ (one or two vertices), the single clause $\bigvee_{u \in \mathrm{pred}(v)} \neg x_u \vee x_v$;
- the unit clause $\neg x_z$ for the sink.

For $G$ with $n$ vertices this is a minimally unsatisfiable CNF formula of width at most $3$ with $n + 1$ clauses over $n$ variables. For a non-constant Boolean function $f$ of arity $\ell$, the **substituted pebbling formula** $\mathrm{Peb}_G[f]$ has variables $x_{v,1}, \dots, x_{v,\ell}$ for each vertex $v$: each positive literal $x_v$ is replaced by the canonical CNF of $f(x_{v,1}, \dots, x_{v,\ell})$, each negative literal $\neg x_v$ by the canonical CNF of $\neg f(x_{v,1}, \dots, x_{v,\ell})$, and each clause is expanded into a CNF by distributing the disjunction. $\mathrm{Peb}_G[f]$ is unsatisfiable and has fewer than $(n + 1) \cdot 2^{3\ell}$ clauses, each of width at most $3\ell$. The usual choices are the two-input OR $\vee_2$ and exclusive or $\oplus_\ell$.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- E. Ben-Sasson, R. Impagliazzo, A. Wigderson, "Near optimal separation of tree-like and general resolution", Combinatorica 24 (2004) 585-603.
- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", Logical Methods in Computer Science 9 (2013) (Definitions 2.11 and 2.12).
