# Probability of a physical configuration

Let $G$ be a graph on a finite vertex set $V$, $J$ a real function on unordered pairs of elements of $V$ and $\beta \in \mathbb{R}$. For a physical configuration $\eta$ (a configuration on the unordered pairs of elements of $V \cup \{\mathfrak{g}\}$ that are not ghost edges), its weight is

$$\prod_{e} p_e^{\eta_e} (1 - p_e)^{1 - \eta_e}, \qquad p_e = 1 - e^{-\beta J'_e},$$

the product over the pairs $e$ that are not ghost edges, where $J'$ is the [lifted coupling](abfa-lift-coupling.md). For $\beta \ge 0$ and $J \ge 0$ on the edges of $G$ it is the probability of $\eta$ under independent bond percolation with parameters $p_e$.
