# Rooted species tree identifiable from unrooted weighted gene trees

**Setting.** A species phylogeny $S = (V_s, E_s; r, \vec\tau, \vec\mu)$ with $n \ge 3$ leaves, edge lengths $\tau_e$ and arbitrary positive edge mutation rates $\mu_e$ (no molecular clock). A gene tree $G$ is drawn from the multispecies coalescent on $S$; its branch $e$ gets the rate-weighted length $\delta_e$, and $\delta_{ab}$ denotes the induced path-length metric on leaves.

**Theorem.** The rooted topology of $S$ is identifiable from the distribution of the *unrooted* weighted gene tree $G$, i.e. from the joint law of the metric $(\delta_{ab})_{a,b \in L}$.

**Key step.** For three leaves and a permutation $(x, y, z)$ of $(1,2,3)$, let $\delta^{(1/2)}_{ab}$ be the median of $\delta_{ab}$ and

$$
\mathscr{E}_I = \big\{ \delta_{xy} \le \delta^{(1/2)}_{xy},\ \delta_{xz} > \delta^{(1/2)}_{xz},\ \delta_{yz} > \delta^{(1/2)}_{yz} \big\}.
$$

Then $\mathscr{E}_I$ has positive probability and forces the rooted gene-tree topology $xy|z$, and

$$
\mathbb{E}\big[\delta_{xz} - \delta_{yz} \mid \mathscr{E}_I\big] = \Delta_{xy} := \mu_{rx} - \mu_{ry}.
$$

So the root-to-leaf differences are identifiable; adding those offsets turns the problem into the clock-like case, where the rooted triple topologies (hence the rooted species tree) are identified.

## Depends on

- [Species tree](../../../../coalescent-theory/multispecies-coalescent/species-tree.md)

## Expansion

On $\mathscr{E}_I$ the gene-tree cherry is $\{x, y\}$, so $z$ attaches above the most recent common ancestor of $x$ and $y$, and $\delta_{xz} - \delta_{yz}$ equals the difference of the rate-weighted lengths from that ancestor down to $x$ and to $y$; the source shows that its conditional expectation is the species-tree offset $\Delta_{xy}$. Knowing all offsets, one corrects the gene metrics to an ultrametric, from which the rooted triple topologies and therefore the rooted species tree are identified.

## Sources

- G. Dasarathy, E. Mossel, R. Nowak, S. Roch, "Coalescent-based species tree estimation: a stochastic Farris transform", arXiv:1707.04300 (2017): Theorem 3 (identifiability of the rooted species tree from unrooted weighted gene trees), Propositions 1–2 (fixing the rooted gene-tree topology and the height-difference formula). <https://doi.org/10.48550/arXiv.1707.04300> Published version: Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01731-5>.
