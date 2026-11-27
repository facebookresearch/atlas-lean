# Public-goods diffusion equilibrium on a weighted graph

Let cells occupy the vertices of a finite, connected, bi-transitive weighted graph $G$ (so in particular $G$ is vertex-transitive and symmetric, $e_{ij} = e_{ji}$) with no self-loops ($e_{ii} = 0$) and edge weights $e_{ij} \ge 0$ normalized so that $\sum_{j} e_{ij} = 1$ for every $i$; $e_{ij}$ is the frequency of diffusion from $i$ to $j$. Each cell has a type $s_i \in \{0, 1\}$, cooperator ($s_i = 1$) or defector ($s_i = 0$), and $\psi_i \ge 0$ denotes the concentration of a diffusible public good at vertex $i$. With production at unit rate by cooperators, utilization at unit rate, and diffusion at rate $\lambda > 0$,

$$\dot{\psi}_i = s_i - \psi_i - \lambda \psi_i + \lambda \sum_{j \in G} e_{ji} \psi_j .$$

**Stationary state.** Setting $\dot\psi_i = 0$ gives the linear recurrence

$$(1 + \lambda)\, \psi_i = s_i + \lambda \sum_{j \in G} e_{ji}\, \psi_j,$$

a diagonally dominant system, hence uniquely solvable with nonnegative solution for every state $s$.

**Retention fractions.** In the state where exactly one cell $i$ is a cooperator, write

$$\phi_0 = \psi_i, \qquad \phi_1 = \sum_{j \in G} e_{ij}\, \psi_j$$

for the share of the good retained by its producer and the edge-weighted average share reaching an immediate neighbour. By symmetry these do not depend on which vertex is chosen. Evaluating the stationary recurrence at the producer gives the identity

$$(1 + \lambda)\,\phi_0 = 1 + \lambda\, \phi_1 .$$

The limits are the expected ones: as $\lambda \to 0$, $\phi_0 \to 1$ and the good is private; as $\lambda \to \infty$, the stationary distribution tends to that of the random walk, which is uniform by the symmetry assumed above, so on a graph of $N$ vertices $\phi_0, \phi_1 \to 1/N$ and the good is shared evenly with the whole population.

**Decay.** If the public good also decays (or escapes) at rate $d$ relative to the utilization rate, so that $\dot\psi_i = s_i - \psi_i - d\,\psi_i - \lambda\psi_i + \lambda\sum_{j \in G} e_{ji}\psi_j$, then $\tilde\psi_i = (1+d)\psi_i$ and $\tilde\lambda = \lambda/(1+d)$ satisfy the same stationary recurrence, so every statement about the model without decay transfers with $\lambda$ replaced by $\tilde\lambda$ and the benefit $b$ divided by $1 + d$.

## Expansion

The operator on the right is $\lambda$ times the transition matrix of the random walk with weights $e_{ji}$, so the stationary equation reads $\big((1+\lambda)I - \lambda P^{\mathsf{T}}\big)\psi = s$ with $P$ stochastic; since $\|\lambda P^{\mathsf{T}}\|_\infty = \lambda < 1 + \lambda$, the matrix is invertible with a convergent Neumann series, giving $\psi = \sum_{n \ge 0} \lambda^n (1+\lambda)^{-n-1} (P^{\mathsf{T}})^n s$. Read entrywise, this says the good reaching a vertex is a geometric-weighted sum over walks from producers, with each additional step discounted by $\lambda/(1+\lambda)$: the diffusion parameter alone sets the decay per step and the graph sets which vertices are reachable in how many ways. That walk representation is what makes $\phi_0$ computable from the random walk's generating function and is the reason the whole model reduces to two scalars per graph.

## Sources

- B. Allen, J. Gore and M. A. Nowak, "Spatial dilemmas of diffusible public goods", eLife 2 (2013), e01169, Model and Results (Eq. (1), Eq. (3), definitions of $\phi_0, \phi_1$) and Materials and methods (Eq. (3), 'Decay of the public good'), <https://doi.org/10.7554/elife.01169>, PMCID PMC3865686.
