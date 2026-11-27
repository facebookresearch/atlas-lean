# Poincaré recurrence of replicator dynamics with coevolving rock–paper–scissors payoffs

**Model.** A population with type frequencies $\mathbf{x} \in \Delta_n$ plays a cyclic $n$-strategy rock–paper–scissors game ($i$ beats $i-1$ and loses to $i+1$, indices mod $n$) whose payoffs are perturbed by a second frequency vector $\mathbf{w} \in \Delta_n$ with strength $\mu > 0$:

$$P^{\mathbf{w}}_{ij} = \mu(w_i - w_j) + \begin{cases} 1 & j \equiv i - 1, \\ -1 & j \equiv i + 1, \\ 0 & \text{otherwise}, \end{cases}$$

an antisymmetric matrix with zero diagonal. The coupled dynamics are

$$x_i' = x_i \sum_j P^{\mathbf{w}}_{ij} x_j, \qquad w_i' = w_i \sum_j w_j (x_j - x_i), \qquad i = 1, \dots, n,$$

so $\mathbf{x}$ follows replicator dynamics under $P^{\mathbf{w}}$, while $\mathbf{w}$ grows in the types that are rare in $\mathbf{x}$ (a zero-sum response, as in a differential game).

**Theorem.** For all initial positions in $\operatorname{int}(\Delta_n) \times \operatorname{int}(\Delta_n)$ outside a set of Lebesgue measure zero, the trajectory returns arbitrarily close to its initial position infinitely often. In particular, no strategy is driven to extinction along such trajectories and the system does not converge to a fixed point.

## Depends on

- [Solution of the replicator equation](../../../replicator-dynamics/is-solution.md)

## Expansion

Map the interior of each simplex to $\mathbb{R}^{n-1}$ by the natural log-ratio transformation $\Pi(\mathbf{y}) = (\log(y_1/y_n), \dots, \log(y_{n-1}/y_n))$, a bijection. In these coordinates $\frac{d}{dt}\log(x_i/x_n) = \sum_j (P^{\mathbf{w}}_{ij} - P^{\mathbf{w}}_{nj})x_j$ and similarly for $\mathbf{w}$; because $P^{\mathbf{w}}$ is antisymmetric with zero diagonal and the $\mathbf{w}$-equation is the zero-sum counterpart of the $\mathbf{x}$-equation, the transformed vector field is divergence-free, so by Liouville's theorem the flow preserves volume. The transformed orbits are moreover bounded (Lemma 4.2). A volume-preserving flow with bounded orbits satisfies the Poincaré recurrence theorem, which gives recurrence for almost every initial point. The conclusion models how a coevolving environment that penalizes common types sustains biological diversity in cyclic competition.

## Sources

- Tung Mai, Milena Mihail, Ioannis Panageas, Will Ratcliff, Vijay Vazirani, Peter Yunker, "Cycles in Zero-Sum Differential Games and Biological Diversity", in Proceedings of the 2018 ACM Conference on Economics and Computation (2018), 339–350, <https://doi.org/10.1145/3219166.3219227>. Published version of arXiv:1710.11249, cited next; locators there refer to the arXiv version.
- Tung Mai, Ioannis Panageas, Will Ratcliff, Vijay V. Vazirani, "Rock-Paper-Scissors, Differential Games and Biological Diversity", arXiv (2017). Definition 3.1, Theorems 3.1, 3.2 and 4.1, Definition 4.1, Lemma 4.2. <https://doi.org/10.48550/arXiv.1710.11249>
