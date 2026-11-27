# Sum of the weighted degrees

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed). For every $w : E \to \mathbb{R}$, the [weighted degree](../../part-02/conductance-and-cheeger-s-inequality/weighted-degree.md) $\pi(x) = \sum_e w_e([e^- = x] + [e^+ = x])$ satisfies

$$\sum_{x \in V} \pi(x) = 2 \sum_{e \in E} w_e,$$

since every edge is counted at both of its ends. In a loopless multigraph this is the constant $\gamma$ of R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Corollary 2.21.
