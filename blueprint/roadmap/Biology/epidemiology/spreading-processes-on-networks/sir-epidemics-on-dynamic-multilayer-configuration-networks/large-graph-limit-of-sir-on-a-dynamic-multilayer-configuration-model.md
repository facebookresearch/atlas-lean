# Large-graph limit of SIR epidemics on a dynamic multilayer configuration model

**Model.** A random multilayer configuration model $\mathcal{G}_r(\psi, n)$ on $n$ nodes has $r$ layers of edges, each layer standing for a mode of transmission. Each node draws a degree vector $\mathbf{k} = (k_1,\dots,k_r)$ from a distribution $(p_{\mathbf{k}})$ with probability generating function $\psi(\mathbf{x}) = \sum_{\mathbf{k}} p_{\mathbf{k}} \mathbf{x}^{\mathbf{k}}$, and half-edges are paired uniformly within each layer. A Markovian SIR epidemic runs on the graph: infection crosses an active layer-$j$ edge from $I$ to $S$ at rate $\beta_j$ and infected nodes recover at rate $\gamma$. The network responds to the epidemic: edges between susceptible and infected nodes in layer $j$ deactivate at rate $\delta_j$ and reactivate at rate $\eta_j$. Layers $1,\dots,m$ start active and layers $m+1,\dots,r$ start inactive.

**Assumptions.** (A1) On $(0,T]$ the number of susceptible half-edges tends to infinity with high probability. (A2) The initial fractions of $S$, $I$, $R$ nodes converge in probability to $\alpha^S, \alpha^I, \alpha^R$ with $\alpha^S, \alpha^I > 0$, the initially infected and recovered nodes being chosen at random. (A3) $\sum_{\mathbf{k}} \|\mathbf{k}\|^2 p_{\mathbf{k}} < \infty$.

**Theorem (strong law of large numbers).** Under (A1)–(A3), for every $0 < T < \infty$, the vector $\mathbf{X}/n$ of scaled node and dyad counts, together with the vector $\boldsymbol\theta$ of per-layer probabilities that a half-edge has not yet transmitted infection, satisfies

$$
\sup_{0 < t \le T} \big\| (\mathbf{X}/n, \boldsymbol\theta)(t) - (\mathbf{x}, \boldsymbol\theta)(t) \big\| \xrightarrow{P} 0,
$$

where $(\mathbf{x}, \boldsymbol\theta)$ solves a closed, finite-dimensional ODE system with $\boldsymbol\theta(0) = \mathbf{1}$ and in which $S(t) = \alpha^S \psi(\boldsymbol\theta(t))$.

**Corollaries.**

1. For a static network ($\delta_j = \eta_j = 0$), the limit is the edge-based model with multiple modes of transmission:

$$
\frac{d\theta_j}{dt} = -\beta_j \theta_j + \beta_j \alpha^S \frac{\partial_j \psi(\boldsymbol\theta)}{\partial_j \psi(\mathbf{1})} + \gamma (1 - \theta_j) + \beta_j \alpha^R, \qquad \frac{dR}{dt} = \gamma I,
$$

with $S = \alpha^S \psi(\boldsymbol\theta)$ and $I = 1 - S - R$. For $r = 1$ this is the Volz–Miller edge-based SIR model.
2. The limit coincides with the pairwise (pair-approximation) model for $S, I, [SI]_j, [SS]_j$ and their inactive-edge analogues if and only if the degree distribution is of multivariate Poisson type. For a static single layer this is Rand's pairwise SIR model, again exactly when the degree distribution is Poisson-type.

## Depends on

- [Kenah–Robins epidemic percolation networks](../../epidemics-on-networks/kenah-robins-epidemic-percolation-network-exact-isomorphism-of-network.md)

## Expansion

The proof follows a susceptible node's half-edges rather than the whole graph. The quantity $\theta_j(t)$ is the probability that a layer-$j$ half-edge of a susceptible node has not transmitted infection by time $t$, so a node with degree vector $\mathbf{k}$ is still susceptible with probability $\boldsymbol\theta^{\mathbf{k}}$. Its scaled susceptible count therefore concentrates on $\alpha^S p_{\mathbf{k}} \boldsymbol\theta^{\mathbf{k}}$, and the susceptible half-edge count on $\alpha^S \boldsymbol\theta \cdot \nabla\psi(\boldsymbol\theta)$. The dyad counts are semimartingales whose compensators are, up to vanishing error terms, functions of these quantities. Kurtz-type convergence of density-dependent jump processes, combined with the configuration-model pairing, closes the system. For Poisson-type degree distributions the excess-degree factors become constants $\kappa_{ij}$, which makes the pair approximation exact.

## Sources

- Karly A. Jacobsen, Mark G. Burch, Joseph H. Tien, Grzegorz A. Rempała, "The large graph limit of a stochastic epidemic model on a dynamic multilayer network", Journal of Biological Dynamics 12 (2018), 746–788, <https://doi.org/10.1080/17513758.2018.1515993>. Published version of arXiv:1605.02809, cited next; locators there refer to the arXiv version.
- Karly A. Jacobsen, Mark G. Burch, Joseph H. Tien, Grzegorz A. Rempała, "The large graph limit of a stochastic epidemic model on a dynamic multilayer network", arXiv (2016). Theorem 3.1, Corollary 3.2, Corollary 3.3, Corollary 3.4, Corollary 3.5, Lemma B.1, Lemma B.2. <https://doi.org/10.48550/arXiv.1605.02809>
