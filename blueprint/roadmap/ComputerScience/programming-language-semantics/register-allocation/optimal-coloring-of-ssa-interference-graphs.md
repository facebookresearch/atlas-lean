# Optimal coloring of SSA interference graphs

Let $P$ be a strict program in SSA form with interference graph $G$, with the liveness convention of [interference in strict SSA programs](interference-in-strict-ssa-programs.md), and let $\mathrm{maxlive}$ be the largest number of variables live at one label of $P$.

**Theorem.** Coloring the variables greedily in the reverse of the [perfect elimination order given by dominance](dominance-order-gives-a-perfect-elimination-order.md), each with the first color not used by its already colored neighbors, uses exactly $\mathrm{maxlive}$ colors. This is the chromatic number of $G$, which equals the size of its largest clique, and, given the interference graph $G$ and the dominator tree, the coloring is found in time $O(L + V + |E(G)|)$, where $L$ is the number of nodes of the dominator tree and $V$ the number of variables; given the elimination order itself, greedy coloring takes time $O(V + |E(G)|)$, which is $O(V^2)$. The term $L$ cannot be dropped: a program $x \leftarrow 0$ followed by arbitrarily many labels that only use $x$ has one variable and no interference edge, but a dominator tree with one node per label. A variable live on leaving a label is live at a successor label, and a variable is live at the label that defines it, so two variables that interfere in the sense of [interference graphs](interference-graphs.md) are adjacent in $G$; hence the coloring is a register assignment with $\mathrm{maxlive}$ registers. The converse does not hold: in $x \leftarrow 1;\ y \leftarrow x + 1;\ \mathtt{return}\ y$, both $x$ and $y$ are live at the middle label in this sense, so $\mathrm{maxlive} = 2$, yet one register suffices because $y$ can overwrite $x$.

**Proof.** By [greedy coloring along a perfect elimination order](greedy-coloring-along-a-perfect-elimination-or.md) the coloring uses as many colors as the largest clique, which has $\mathrm{maxlive}$ variables by [the clique property](cliques-in-ssa-interference-graphs.md). A postorder walk of the dominator tree lists the variables in that order in time $O(L + V)$, and coloring each variable inspects its neighbors once, in time $O(V + |E(G)|) = O(V^2)$ in total.

## Depends on

- [Interference graphs](interference-graphs.md)
- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)
- [Interfering variables of a strict SSA program are simultaneously live](cliques-in-ssa-interference-graphs.md)
- [Dominance order gives a perfect elimination order](dominance-order-gives-a-perfect-elimination-order.md)

## Proof depends on

- [Greedy coloring along a perfect elimination order](greedy-coloring-along-a-perfect-elimination-or.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3: the greedy reinsertion coloring along a perfect elimination order, the consequence that SSA interference graphs can be colored optimally in quadratic time, and the remark after Theorem 2 that the chromatic number is determined by the largest clique.
- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>: the abstract and Section 1.2 (Bouchez, Brisk and Hack proved independently that the interference graphs of SSA programs are chordal).
