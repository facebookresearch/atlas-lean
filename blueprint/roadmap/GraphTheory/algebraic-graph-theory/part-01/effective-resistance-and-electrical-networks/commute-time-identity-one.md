# Commute-time identity for unit conductances

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with connected [underlying graph](../oriented-incidence-matrices/underlying-graph.md). Give every edge conductance $1$, and for $a, z \in V$ let $h_a$ and $h_z$ solve the [first-step equations](is-hitting-time-solution.md) of the hitting times of $a$ and of $z$. Then

$$h_z(a) + h_a(z) = 2 \lvert E\rvert\, R_{\mathrm{eff}}(a, z),$$

where $R_{\mathrm{eff}}$ is the [effective resistance](effective-resistance.md) for unit conductances (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Corollary 2.21 with $c \equiv 1$).

For a connected simple graph with $m$ edges, the effective resistance across an edge is at most $1$ ([Thomson's principle](effective-resistance-le-flow-energy.md) applied to the unit flow along that edge), so $h_z(a) + h_a(z) \le 2m$ when $a$ and $z$ are adjacent. On the path $0 - 1 - 2$ the solutions give $h_2(0) + h_0(2) = 4 + 4 = 8 = 2 \cdot 2 \cdot 2$.
