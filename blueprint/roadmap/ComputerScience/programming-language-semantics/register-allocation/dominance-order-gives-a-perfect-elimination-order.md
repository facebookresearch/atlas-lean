# Dominance order gives a perfect elimination order

Let $P$ be a strict program in SSA form with interference graph $G$, in the sense of [interference in strict SSA programs](interference-in-strict-ssa-programs.md), with [simplicial vertices and perfect elimination orders](perfect-elimination-orders-and-chordal-graphs.md) as usual.

**Theorem.** A variable $v$ can be added to a perfect elimination order of $G$ once every variable whose defining label is strictly dominated by $D_v$ has been added: $v$ is then simplicial in the graph of the variables not yet added. Hence listing the variables in a postorder walk of the dominator tree, ordered by their defining labels, gives a perfect elimination order, and $G$ is chordal.

**Proof.** If $v$ were not simplicial, it would have two neighbors $a$ and $b$, not yet added, that do not interfere. The defining label of $a$ is not strictly dominated by $D_v$, so by [the comparability lemma](interfering-ssa-variables-have-comparable-defi.md) $D_a$ dominates $D_v$. By [the lemma on non-adjacent pairs](a-non-adjacent-pair-orders-ssa-definitions.md), applied to $a v, v b \in E$ and $ab \notin E$, $D_v$ strictly dominates $D_b$, contradicting the choice of $b$.

## Depends on

- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)
- [Perfect elimination orders and chordal graphs](perfect-elimination-orders-and-chordal-graphs.md)

## Proof depends on

- [Interfering SSA variables have comparable definitions](interfering-ssa-variables-have-comparable-defi.md)
- [A non-adjacent pair orders SSA definitions](a-non-adjacent-pair-orders-ssa-definitions.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3: Theorem 2 and its proof, and the remark that a postorder walk of the dominance tree yields a perfect elimination order.
