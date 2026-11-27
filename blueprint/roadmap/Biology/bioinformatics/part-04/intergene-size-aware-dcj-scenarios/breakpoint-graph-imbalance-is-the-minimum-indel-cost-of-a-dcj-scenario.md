# Breakpoint graph imbalance is the minimum indel cost of a DCJ scenario

**Setting.** A genome on a vertex set $V$ of $2n$ gene extremities is a perfect matching $g$ on $V$ (its edges are adjacencies); it is *weighted* if each edge carries a non-negative integer intergene size $w(e)$. A DCJ replaces edges $ab, cd$ by $ac, bd$; a *weighted DCJ* (wDCJ) does the same and assigns sizes with $w(ac) + w(bd) = w(ab) + w(cd)$. An *indel* of size $\delta > 0$ changes one edge weight by $\delta$. For genomes $g_1, g_2$ on $V$, the breakpoint graph $BG(g_1, g_2) = (V, g_1 \cup g_2)$ is a disjoint union of even cycles; a cycle of length two is *trivial*, and *balanced* if its two edges have equal weight. A DCJ is *valid* if it increases the number of cycles by one; valid scenarios have the minimum number $n - c$ of DCJs, $c$ being the number of cycles. For a path or cycle $P$ let $w_i(P) = \sum_{e \in P \cap g_i} w(e)$ and $I(P) = w_1(P) - w_2(P)$; the *imbalance* of the breakpoint graph is $I(BG(g_1, g_2)) = \sum_{C} |I(C)|$ over its cycles. The problem *sorting by wDCJs and indels in intergenes* asks for a valid wDCJ scenario with indels transforming $g_1$ into $g_2$ (all cycles trivial and balanced) whose total indel size $c(g_1, g_2)$ is minimum.

**Results.**

1. No valid wDCJ decreases the imbalance; a valid wDCJ that keeps it unchanged (steady) acts on a *bounded* pair of edges, and every bounded pair supports a valid steady wDCJ. If $e_m$ is an edge of minimum weight in a non-trivial cycle, its two neighbouring edges form a bounded pair.
2. Every valid wDCJ scenario with indels has cost $c(g_1, g_2) \ge I(BG(g_1, g_2))$.
3. An $O(n \log n)$ algorithm, repeatedly applying a steady wDCJ to the neighbours of a minimum-weight edge and then balancing trivial cycles by indels, outputs a valid scenario of cost exactly $I(BG(g_1, g_2))$. Hence the minimum indel cost among DCJ-optimal scenarios equals the breakpoint graph imbalance.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

A pair $(e, f)$ of $g_1$-edges in a cycle $C$, splitting it into paths $P_1, P_2$ with $W = w(e) + w(f)$, is bounded when each $P$ satisfies $I(P) \ge -W$ if $I(C) \ge 0$ and $I(P) \le 0$ if $I(C) \le 0$; this is exactly the condition under which $W$ can be split between the two new edges so that the two new cycles have imbalances of the same sign as $C$, preserving the total absolute imbalance. Since a wDCJ preserves total weight, indels are the only way to remove imbalance, giving the lower bound; the minimum-weight-edge rule always finds a bounded pair, so the bound is attained.

## Sources

- L. Bulteau, G. Fertin and E. Tannier, "Genome rearrangements with indels in intergenes restrict the scenario space", *BMC Bioinformatics* (2016), Statement of the problem, Definition 1, Lemmas 1–2, Corollary 1 and Theorem 1. <https://doi.org/10.1186/s12859-016-1264-6> (PMC5123244)
