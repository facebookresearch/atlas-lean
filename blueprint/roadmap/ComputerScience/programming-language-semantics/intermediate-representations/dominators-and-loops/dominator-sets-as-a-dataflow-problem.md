# Dominator sets as a dataflow problem

Let $G = (N, E, n_0)$ be a finite control-flow graph with entry node $n_0$ in which every node is reachable from $n_0$, and let $\mathrm{Dom}(n)$ be the set of nodes that [dominate](../dominance-and-static-single-assignment-form.md) $n$, so that $n \in \mathrm{Dom}(n)$.

1. **Equations.** The sets $\mathrm{Dom}(n)$ satisfy

    $$\mathrm{Dom}(n_0) = \{n_0\}, \qquad \mathrm{Dom}(n) = \{n\} \cup \bigcap_{p \in \mathrm{preds}(n)} \mathrm{Dom}(p) \quad (n \ne n_0).$$

2. **Greatest solution.** Among all families of sets $D(n) \subseteq N$ satisfying these equations, $(\mathrm{Dom}(n))_n$ is the greatest under pointwise inclusion. If moreover $n_0$ has no predecessors, it is also the meet-over-all-paths solution, in the sense of [the comparison of the two solutions](../../static-analysis/meet-over-all-paths-versus-the-fixed-point.md), of this forward analysis over $(\mathcal{P}(N), \supseteq)$, whose transfer functions $S \mapsto \{n\} \cup S$ are distributive.
3. **Iteration.** Starting from $D(n) = N$ for every $n \ne n_0$ and repeatedly replacing each $D(n)$ by the right-hand side of its equation, in any order, reaches $(\mathrm{Dom}(n))_n$ after finitely many changes.

**Proof sketch.** Part 1: a dominator of $n \ne n_0$ other than $n$ lies on every path to every predecessor of $n$, and conversely a node on every path to every predecessor lies on every path to $n$. Part 2: every solution satisfies $D(n) \subseteq \mathrm{Dom}(n)$, by induction on the length of a path from $n_0$ to $n$, and the meet over all paths from $n_0$ to $n$ of the sets of nodes on the path is $\mathrm{Dom}(n)$ by definition. Part 3 follows from monotonicity and finiteness of the lattice.

## Depends on

- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)
- [The meet-over-all-paths solution versus the fixed-point solution](../../static-analysis/meet-over-all-paths-versus-the-fixed-point.md)

## Sources

- L. Georgiadis, R. E. Tarjan and R. F. Werneck, "Finding dominators in practice", *Journal of Graph Algorithms and Applications* 10(1):69–94, 2006, doi:10.7155/jgaa.00119, Section 2.1, p. 72: the equations $\mathrm{Dom}'(v) = \bigcap_{u \in \mathrm{pred}(v)} \mathrm{Dom}'(u) \cup \{v\}$ for a root without incoming arcs, $\mathrm{Dom}$ as their unique maximal solution, and the iteration of Allen and Cocke from $\mathrm{Dom}'(r) = \{r\}$ and $\mathrm{Dom}'(v) = V$ otherwise.
- K. D. Cooper, T. J. Harvey and K. Kennedy, *A Simple, Fast Dominance Algorithm*, Rice University Computer Science Technical Report TR-06-33870: section "The Data-flow Approach" (the equations for $\mathrm{Dom}$, the iterative algorithm of Figure 1 with every set initialized to all nodes) and section "Properties of the Iterative Framework" (the framework is distributive, so iteration finds the maximal fixed-point solution, which equals the meet-over-all-paths solution and matches the definition of $\mathrm{Dom}$).
- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: section "Dominator dataflow analysis" (the equations $\mathit{out}[n] = \{n\} \cup \bigcap_{n' \prec n} \mathit{out}[n']$ and $\mathit{out}[\mathtt{start}] = \{\mathtt{start}\}$, solved forward from the set of all nodes with a distributive transfer function).
