# Optimal coloring of SSA interference graphs

Let $P$ be a strict program in SSA form with interference graph $G$, with the liveness convention of [the clique property](cliques-in-ssa-interference-graphs.md), and let $\mathrm{maxlive}$ be the largest number of variables live at one label of $P$.

**Theorem.** Coloring the variables greedily in the reverse of the [perfect elimination order given by dominance](dominance-order-gives-a-perfect-elimination-order.md), each with the first color not used by its already colored neighbors, uses exactly $\mathrm{maxlive}$ colors. This is the chromatic number of $G$, which equals the size of its largest clique, and the coloring is found in quadratic time. A variable live on leaving a label is live at a successor label, and a variable is live at the label that defines it, so two variables that interfere in the sense of [interference graphs](interference-graphs.md) are adjacent in $G$; hence the coloring is a register assignment with $\mathrm{maxlive}$ registers. The converse does not hold: in $x \leftarrow 1;\ y \leftarrow x + 1;\ \mathtt{return}\ y$, both $x$ and $y$ are live at the middle label in this sense, so $\mathrm{maxlive} = 2$, yet one register suffices because $y$ can overwrite $x$.

**Proof.** When a variable is colored, its colored neighbors come after it in the elimination order, so they form a clique together with it; the color chosen is therefore at most the size of the largest clique. That size is $\mathrm{maxlive}$ by [the clique property](cliques-in-ssa-interference-graphs.md), and every coloring needs at least that many colors, since the variables live at one label pairwise interfere.

## Depends on

- [Interference graphs](interference-graphs.md)
- [Interfering variables of a strict SSA program are simultaneously live](cliques-in-ssa-interference-graphs.md)
- [Dominance order gives a perfect elimination order](dominance-order-gives-a-perfect-elimination-order.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3: the greedy reinsertion coloring along a perfect elimination order, bounded by the size of the largest clique; the consequence that SSA interference graphs can be colored optimally in quadratic time; and the remark after Theorem 2 that the chromatic number is determined by the largest clique, which by Theorem 1 corresponds to a label where all its variables are live.
- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>: the abstract and Section 1.2 (Bouchez, Brisk and Hack proved independently that the interference graphs of SSA programs are chordal).
