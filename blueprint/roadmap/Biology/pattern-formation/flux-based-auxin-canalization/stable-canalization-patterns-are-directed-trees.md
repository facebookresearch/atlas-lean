# Stable canalization patterns are directed trees

**Setting.** Consider the slow flux-based auxin transport system on a graph of regular cells,

$$\dot a_i=\alpha_{a_i}-\beta_{a_i}a_i+\sum_{k\sim i}(a_kp_{ki}-a_ip_{ik}),\qquad \dot p_{ij}=\lambda\frac{\alpha_p}{\beta_p}\Phi(a_ip_{ij}-a_jp_{ji})-\mu p_{ij},$$

with quadratic response $\Phi(x)=x^2$ for $x>0$ and $\Phi(x)=0$ for $x\le0$. Put $c=\lambda\alpha_p/(\mu\beta_p)$. Each equilibrium $(a^*,P^*)$ defines an oriented subgraph $\mathcal G^*$ with an arc $i\to j$ iff $p^*_{ij}>0$. Let $E_0$ be the equilibrium with all $p_{ij}=0$ and $a_i=\alpha_{a_i}/\beta_{a_i}$ (all cells isolated). A sink is a cell of $\mathcal G^*$ with incoming but no outgoing arcs.

**Theorem.** Assume $\alpha_{a_i}>0$, $\beta_{a_i}\ge0$ for all $i$, and $\mu,c>0$. Let $(a^*,P^*)\ne E_0$ be a bounded equilibrium with oriented subgraph $\mathcal G^*$. Then

1. if $\mathcal G^*$ contains no sink cell, $(a^*,P^*)$ is unstable;
2. if $(a^*,P^*)$ is stable, $\mathcal G^*$ is a forest of trees directed from leaves to roots in which every cell has out-degree at most 1.

**Steady-state auxin along a tree (sink-driven systems).** Call the system sink-driven if auxin is degraded only in one cell $i_0$: $\beta_{a_{i_0}}>0$ and $\beta_{a_i}=0$ for $i\ne i_0$. Suppose moreover that $\mathcal G^*$ is a stable tree spanning all cells with root (sink) $i_0$, let $V_i^*$ be the set of cells of the subtree draining into $i$ (including $i$), and let $\alpha_a(i)=\sum_{j\in V_i^*}\alpha_{a_j}$ be its total auxin production. Then

$$a^*_i=\frac{1}{c\,\alpha_a(i)}\quad(i\ne i_0),\qquad a^*_{i_0}=\frac{\alpha_a(i_0)}{\beta_{a_{i_0}}},$$

so auxin decreases along every path towards the sink up to the last cell before $i_0$, i.e. flux runs against the auxin gradient inside sink-driven trees away from the sink; the last step into $i_0$ can increase, since $a^*_{i_0}$ is large when $\beta_{a_{i_0}}$ is small (the source: "the auxin concentration decreases along the paths as long as $i\ne i_0$").

## Expansion

Heuristically, at a stable equilibrium each cell can export through at most one membrane: two outgoing arcs from one cell compete for the same auxin, and the quadratic positive feedback makes the split unstable, so one carrier wins. Out-degree at most one together with acyclicity (a directed cycle contains no sink) leaves only in-trees pointing at sinks, which is the observed open, loopless venation. Setting $\dot p_{ij}=0$ on an arc gives $p^*_{ij}=c\,J_{i\to j}^2$, and combining this with $J_{i\to j}=a^*_ip^*_{ij}$ and the auxin balance along the tree yields the closed-form concentrations (derived in the S1 Text): with no degradation outside $i_0$, the flux out of $i$ equals the production $\alpha_a(i)$ of its subtree. With degradation along the tree that flux is smaller and the formula no longer holds. For a source-driven line $i_0\to\dots\to i_n$ the paper shows two parameter regimes, flux along or against the gradient, so canals can hold auxin above the background level $\alpha/\beta$. With a bounded response, simulations instead show stable loops.

## Depends on

- [Flux-based auxin transport model and finite-time PIN divergence](flux-based-auxin-transport-model-and-finite-time-pin-divergence.md)

## Sources

- C. Feller, E. Farcot, C. Mazza, "Self-organization of plant vascular systems: claims and counter-claims about the flux-based auxin transport model", *PLoS ONE* 10(3):e0118238 (2015), Theorem 1, section "Stable steady state topologies", and section "Sink-driven system", equations (4)–(5), <https://doi.org/10.1371/journal.pone.0118238>, PMCID: PMC4348546.
