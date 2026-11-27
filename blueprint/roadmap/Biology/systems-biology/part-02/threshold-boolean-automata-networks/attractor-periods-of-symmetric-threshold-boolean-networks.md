# Attractor periods of symmetric threshold Boolean networks

**Threshold Boolean automata network.** A network of $n$ genes (or neurons) has states $x_i\in\{0,1\}$, an interaction matrix $W = (w_{ij})\in\mathbb{R}^{n\times n}$ ($w_{ij} > 0$: $j$ activates $i$; $w_{ij} < 0$: $j$ represses $i$; $w_{ij} = 0$: no arc) and thresholds $\theta\in\mathbb{R}^n$. The local transition function is

$$f_i(x) = H\Big(\sum_{j=1}^n w_{ij}x_j - \theta_i\Big),$$

with $H$ the Heaviside step function ($H(u) = 1$ if $u > 0$, else $0$). An *iteration mode* fixes the order of local updates: *parallel* (all nodes at once), *sequential* (one node at a time in a fixed cyclic order) or *block-sequential* (an ordered partition of the nodes into blocks, nodes within a block updated simultaneously, blocks in order).

**Attractors and basins.** The configuration space $\{0,1\}^n$ is finite and the global map is deterministic, so every trajectory reaches either a fixed point or a limit cycle; these are the attractors, and the number of configurations in one is its period. The attraction basin of an attractor is the set of configurations that reach it; its relative size $|B|/2^n$ is the probability that a uniformly random initial configuration ends in that attractor, a gauge of the attractor's robustness.

**Theorem 1 (symmetric interactions, parallel iteration).** If $W$ is symmetric, then under parallel iteration every attractor has period $1$ or $2$.

**Theorem 2 (symmetric interactions, sequential iteration).** If $W$ is symmetric with non-negative diagonal ($w_{ii}\ge 0$), then under any sequential iteration mode every attractor is a fixed point.

**Use on regulatory networks.** For a regulatory network whose non-trivial strongly connected components are symmetric (after removing arcs that do not change the asymptotic dynamics), these results bound the possible cell-fate attractors. In the floral morphogenesis network of *Arabidopsis thaliana*, the asymptotically equivalent reduced network has two symmetric strongly connected components, explaining why sequential iteration yields only fixed points while other modes can also yield 2-cycles; clamping a boundary (source) gene, such as one controlled by gibberellin, changes the relative basin sizes of the floral-organ attractors.

## Expansion

Both theorems follow from Lyapunov (energy) functionals. For the sequential mode, $E(x) = -\tfrac12\sum_{i,j}w_{ij}x_ix_j + \sum_i\theta_ix_i$ does not increase when a single node is updated, and it strictly decreases whenever the node changes state (the tie case $u = 0$ always yields $0$, and $w_{ii}\ge 0$ controls the self-term), so no cycle of length greater than one can occur. For the parallel mode, the two-step functional $E(x(t), x(t-1)) = -\sum_{i,j}w_{ij}x_i(t)x_j(t-1) + \sum_i\theta_i\big(x_i(t) + x_i(t-1)\big)$ is non-increasing and strictly decreases unless $x(t+1) = x(t-1)$, which forces period at most two.

## Sources

- J. Demongeot, E. Goles, M. Morvan, M. Noual, S. Sené, *Attraction basins as gauges of robustness against boundary conditions in biological complex systems*, PLoS ONE 5 (2010), e11793, "Preliminary definitions", "Threshold Boolean automata networks as a model of regulation networks dynamics", "Original Mendoza & Alvarez-Buylla Network" (Theorems 1–2, Proposition 1, reduced network) and "Variation around the Original Mendoza & Alvarez-Buylla Network: the Toy Model". <https://doi.org/10.1371/journal.pone.0011793> (PMCID: PMC2916819)
