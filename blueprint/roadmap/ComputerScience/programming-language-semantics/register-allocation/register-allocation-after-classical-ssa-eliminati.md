# Register allocation after classical SSA elimination is NP-complete

*Classical SSA elimination* replaces each $\varphi$-function $v = \varphi(v_1, \dots, v_m)$ of a program in [SSA form](../intermediate-representations/dominance-and-static-single-assignment-form.md) by copy instructions $v = v_i$ at the end of the predecessor blocks. A *simple post-SSA program* is a program of the following form, which classical SSA elimination produces from an SSA program with one loop: it takes parameters $p_1, \dots, p_{K+1}$, copies them by $\mathtt{int}\ v_{1j} = p_j$ for $j \le K$ and $\mathtt{int}\ i_1 = p_{K+1}$, executes the copies $\mathtt{int}\ v_j = v_{1j}$ for $j \le K$ and $\mathtt{int}\ i = i_1$, and then runs

$$\mathtt{while}\ (i < C)\ \{\ \mathtt{int}\ i_2 = i + 1;\ S^*;\ v_1 = v_{21}; \dots; v_K = v_{2K};\ i = i_2;\ \}\quad \mathtt{return}\ v_1;$$

where $C$ ranges over integer constants and every statement $S$ of the body is $\mathtt{int}\ v_j = i + C$, $v_j = v_k$ or $\mathtt{if}\ (v_j > C)\ \mathtt{break}$.

**Theorem.** The [core register allocation problem](interference-graphs.md), with the number $K$ of registers part of the input, is NP-complete for simple post-SSA programs.

The proof reduces the coloring problem for [circular-arc graphs](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-coloring-variants/circular-arc-coloring-np-complete.md), given by their representation $V$ as a set of arcs $(d, u)$ with integer endpoints, $\min(V)$ being the smallest endpoint used: when $\min(V) > K$, $V$ is $K$-colorable if and only if an associated *SSA-circular* graph $F(V, K)$ is, and an SSA-circular graph $Y$ is $K$-colorable if and only if the core register allocation problem has a solution for an associated simple post-SSA program $H(Y, K)$ with $K + 1$ registers. The result holds whatever the order in which the copies are inserted. So, although register allocation is polynomial for [strict SSA programs](optimal-coloring-of-ssa-interference-graphs.md), translating to SSA form, allocating registers and then eliminating SSA classically does not give a polynomial algorithm unless P = NP.

## Depends on

- [Interference graphs](interference-graphs.md)
- [Dominance and static single assignment form](../intermediate-representations/dominance-and-static-single-assignment-form.md)
- [Optimal coloring of SSA interference graphs](optimal-coloring-of-ssa-interference-graphs.md)

## Proof depends on

- [CIRCULAR-ARC GRAPH COLORING is NP-complete](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-coloring-variants/circular-arc-coloring-np-complete.md)

## Sources

- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>: the abstract; Section 1.1 (the core register allocation problem, SSA form and post-SSA programs, Figure 3 with the grammar of simple post-SSA programs); Section 2 (circular and SSA-circular graphs, Lemmas 1–4); Section 3 (Lemma 5 and Theorem 1); and the remark after Theorem 1 on the order of copy insertion.
