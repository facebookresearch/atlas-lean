# Dominance order gives a perfect elimination order

Let $P$ be a strict program in SSA form with interference graph $G$, as in [the clique property of SSA interference graphs](cliques-in-ssa-interference-graphs.md). A vertex of a graph is *simplicial* if its neighbors form a clique, and a *perfect elimination order* lists the vertices so that each is simplicial in the subgraph induced by itself and the vertices after it.

**Theorem.** A variable $v$ can be added to a perfect elimination order of $G$ once every variable whose defining label is strictly dominated by $D_v$ has been added: $v$ is then simplicial in the graph of the variables not yet added. Hence listing the variables in a postorder walk of the dominator tree, ordered by their defining labels, gives a perfect elimination order, and $G$ is *chordal*.

**Proof.** If $v$ were not simplicial, it would have two neighbors $a$ and $b$, not yet added, that do not interfere. Their defining labels are not strictly dominated by $D_v$, since all such variables have been added, so by part 1 of [the clique property](cliques-in-ssa-interference-graphs.md) $D_a$ and $D_b$ dominate $D_v$, possibly being equal to it. By part 2 of that page, applied to the pairs $(a, v)$ and $(b, v)$, both $a$ and $b$ are live at $D_v$, so they interfere, a contradiction.

## Depends on

- [Interfering variables of a strict SSA program are simultaneously live](cliques-in-ssa-interference-graphs.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3: simplicial nodes and perfect elimination orders, Lemma 3, Theorem 2 and its proof, and the remark that a postorder walk of the dominance tree yields a perfect elimination order and that graphs with such orders are the chordal graphs.
