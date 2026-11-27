# The spill everywhere problem

Let $G = (V, E)$ be the interference graph of a program, an *interval graph*, the intersection graph of the live intervals, for straight-line code and a chordal graph, in the sense of [perfect elimination orders and chordal graphs](perfect-elimination-orders-and-chordal-graphs.md), for a strict SSA program, with a weight $w(v) \ge 0$ for each variable. Let $\Omega$, also called Maxlive, be the size of the largest clique, the register pressure, and let $r$ be the number of registers. The *spill everywhere problem without holes* asks for a set $W \subseteq V$ of minimum total weight whose removal leaves a graph whose largest clique has size at most $r$: a spilled variable frees its register on its whole live range. Variants restrict the target pressure to $\Omega - 1$ (the *incremental* problem), to $\Omega - k$ for a constant $k$, or to a constant $r$ (*few registers*), and distinguish the unweighted case $w = 1$ from the weighted one. In the problem *with holes*, a spilled variable still occupies a register at its definition and uses.

## Depends on

- [Perfect elimination orders and chordal graphs](perfect-elimination-orders-and-chordal-graphs.md)

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", *Proceedings of the 2007 ACM SIGPLAN/SIGBED Conference on Languages, Compilers, and Tools for Embedded Systems (LCTES 2007)*, ACM, 2007, pp. 103–112, doi:10.1145/1254766.1254782, author copy with the same theorem numbering arXiv:0710.3642v1 <https://arxiv.org/abs/0710.3642>, Section 2: the configurations (basic blocks give interval graphs, strict SSA gives chordal graphs), the models with and without holes, weighted and unweighted costs, Maxlive $\Omega$, the four targets $\Omega' \le \Omega - 1$, $\Omega' \le \Omega - k$, $\Omega' \le k$ and $\Omega' \le r$, and the formulation as a node deletion problem.
