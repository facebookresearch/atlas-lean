# Fixation probability on switching temporal networks

**Setting.** $N$ individuals occupy the nodes of a network; residents have fitness $1$ and mutants fitness $r > 0$. Under *birth–death updating*, at each step an individual is chosen to reproduce with probability proportional to fitness and its offspring replaces a neighbour chosen with probability proportional to edge weight. In a *switching network* $(G_1, G_2, \tau)$ the contact network alternates between the static networks $G_1$ and $G_2$ on the same node set, every $\tau$ time steps (or at Markovian random times). Let $\rho$ be the fixation probability of a single mutant placed uniformly at random, and compare with the Moran (complete-graph) value
$$
\rho_{\mathrm{Moran}} = \frac{1 - 1/r}{1 - 1/r^{N}} .
$$
A network is an *amplifier* of selection if $\rho > \rho_{\mathrm{Moran}}$ for $r > 1$ and $\rho < \rho_{\mathrm{Moran}}$ for $r < 1$, a *suppressor* if the reverse holds, and *isothermal* if $\rho = \rho_{\mathrm{Moran}}$.

**Results.**
1. *(Neutral drift.)* If $r = 1$, then $\rho = 1/N$ for all $G_1$, $G_2$ and $\tau \in \mathbb{N}$.
2. *(Isothermal switching.)* If $G_1$ and $G_2$ are both isothermal (for undirected, possibly weighted networks: all nodes have equal weighted degree), then the switching network $(G_1, G_2, \tau)$ is isothermal.
3. *(Computation.)* For small $N$ the fixation probability is computed exactly by solving the linear system for the Markov chain on (mutant set, network phase) states. In most cases switching networks are less amplifying than both constituent static networks, and most switching networks on at most six nodes are suppressors, although most static networks are amplifiers under birth–death updating with uniform initialization.

## Depends on

- [Isothermal theorem for evolutionary graph dynamics](../isothermal-theorem-for-evolutionary-graph-dynami/README.md)

## Expansion

With $r = 1$ the expected fraction of the population descended from any one individual is preserved by every birth–death step, whatever the current graph, so the initial share $1/N$ is the fixation probability. On an isothermal graph the number of mutants $m$ performs a birth–death chain with $p_{m,m+1}/p_{m,m-1} = r$ regardless of which nodes are mutants, and this ratio is the same in both phases, so switching between two isothermal graphs gives exactly the Moran chain. For general graphs, switching mixes the spatial configuration that favours mutants in one graph with a configuration that disfavours them in the other, which typically erodes amplification.

## Sources

- J. Bhaumik, N. Masuda, "Fixation probability in evolutionary dynamics on switching temporal networks", arXiv:2304.00170 (2023), Theorems 1–2 and the definitions of amplifier, suppressor and isothermal networks, <https://doi.org/10.48550/arXiv.2304.00170>.
