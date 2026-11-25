# Coalescing random walks dual to the voter model on a finite graph

Let $G$ be a finite connected graph with at least two vertices. In the voter model on $G$, each vertex at rate $1$ adopts the opinion of a uniformly chosen neighbour. For coalescing random walks on $G$, each walk jumps at rate $1$ to a uniformly chosen neighbour, and two walks that meet move together from then on.

1. **Duality.** For deterministic initial opinions $\eta_0$ and every $t \ge 0$, the configuration $(\eta_t(x))_{x}$ has the law of $(\eta_0(X^x_t))_{x}$, where $(X^x)_{x}$ are coalescing random walks started from the vertices of $G$, one from each.
2. **Identity in state.** If the initial opinions are independent and identically distributed, with probability $s$ that two of them agree, then for vertices $x \ne y$

$$\mathbb{P}\bigl(\eta_t(x) = \eta_t(y)\bigr) = \mathbb{P}(\tau_{xy} \le t) + s\, \mathbb{P}(\tau_{xy} > t),$$

where $\tau_{xy}$ is the meeting time of the walks started at $x$ and $y$.

A single vertex is trivially absorbing and is excluded.

## Depends on

- [Finite simple graph](../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)

## Proof depends on

- [Finite interacting particle systems: existence, graphical construction and voter duality](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/finite-interacting-particle-systems-graphical-co.md)
- [Structured coalescent for n lineages with a general migration matrix](structured-coalescent-for-n-lineages-with-a-gene.md)

## Expansion

1. The graphical construction of the voter model from Poisson clocks and its time reversal, which gives the duality.
2. The identity-in-state formula from the duality, conditioning on whether the two walks have met by time $t$.
3. A check: on the complete graph the meeting of the walks reduces to the Moran model and Kingman's coalescent after scaling.

## Sources

- T. M. Liggett, *Interacting Particle Systems*, Springer (1985) (voter duality).
- J. T. Cox and R. Durrett, The stepping stone model: new formulas expose old myths, *Ann. Appl. Probab.* 12 (2002), 1348–1377 (stepping stone model).
