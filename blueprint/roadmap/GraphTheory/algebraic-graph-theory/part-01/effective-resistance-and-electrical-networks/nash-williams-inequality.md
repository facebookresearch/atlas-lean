# The Nash-Williams inequality

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with conductances $w : E \to (0, \infty)$. Let $a \ne z$ be vertices in the same connected component of the [underlying graph](../oriented-incidence-matrices/underlying-graph.md), and let $(C_k)_{k \in s}$ be a finite family of pairwise disjoint edge sets, each [separating](separating-edge-set.md) $a$ from $z$. Then

$$\sum_{k \in s} \Big(\sum_{e \in C_k} w_e\Big)^{-1} \le R_{\mathrm{eff}}(a, z),$$

where $R_{\mathrm{eff}}$ is the [effective resistance](effective-resistance.md) (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.5, the Nash-Williams Inequality (2.13)). Since $a$ and $z$ are connected, every separating set is nonempty, so each term on the left is finite and positive.

This is the source's inequality for two vertices of a finite network, with the cutsets indexed by a finite set, under two additional hypotheses: looplessness, and connectivity of $a$ and $z$ (for disconnected vertices the source has $R(a \leftrightarrow z) = \infty$). On the path $0 - 1 - 2$ with unit conductances, the two single-edge cutsets give $1 + 1 \le R_{\mathrm{eff}}(0, 2) = 2$, with equality.

## Background

- [Thomson's principle](effective-resistance-le-flow-energy.md): the effective resistance is the energy of the unit current, which the proof bounds from below cutset by cutset.
