# Flux parametrization of the disguised toric locus

An *E-graph* is a finite simple directed graph $G = (V,E)$ with $V \subseteq \mathbb{Z}^n$; with rate constants $\kappa \in \mathbb{R}^{|E|}_{>0}$ it defines the mass-action system $\dot x = f_{(G,\kappa)}(x) = \sum_{y \to y' \in E} \kappa_{y\to y'} x^{y} (y' - y)$ on $\mathbb{R}^n_{>0}$, with stoichiometric subspace $\mathcal{S} = \operatorname{span}\{y'-y\}$. $(G,\kappa)$ is *vertex-balanced* (complex-balanced) if some $x^* > 0$ satisfies $\sum_{y \to y_0} \kappa_{y\to y_0} (x^*)^{y} = \sum_{y_0 \to y'} \kappa_{y_0 \to y'} (x^*)^{y_0}$ for every vertex $y_0$. Two pairs $(G,\kappa)$ and $(H,\lambda)$ are *dynamically equal* if $f_{(G,\kappa)} = f_{(H,\lambda)}$, equivalently if for every vertex $y_0 \in V \cup V_H$ the net reaction vectors $\sum_{y_0 \to y'} \kappa_{y_0\to y'} (y'-y_0)$ agree.

The *disguised toric locus* $\mathcal{K}_{\mathrm{disg}}(G)$ is the set of $\kappa$ such that $(G,\kappa)$ is dynamically equal to some vertex-balanced $(H,\lambda)$; on it, the positive equilibria form a log-linear set $\{x : \log x - \log x^* \in \mathcal{S}_H^\perp\}$ with exactly one point in each class $(x_0 + \mathcal{S}_H)_{>0}$, and the Horn-Jackson function is a Lyapunov function.

A *flux* on $G$ is $\beta \in \mathbb{R}^{|E|}_{>0}$; it is *vertex-balanced* if inflow equals outflow at every vertex, and these form the toric flux cone $\mathcal{F}_{\mathrm{t}}(H)$. The *disguised toric flux cone* is

$$\mathcal{F}_{\mathrm{disg}}(G) = \{\beta \in \mathbb{R}^{|E|}_{>0} : (G,\beta) \text{ is dynamically equal to some } (H,\gamma) \text{ with } \gamma \in \mathcal{F}_{\mathrm{t}}(H)\},$$

the positive part of a pointed polyhedral cone, computable by linear programming.

**Theorem.** Suppose $\mathcal{K}_{\mathrm{disg}}(G) \ne \emptyset$ and that the kinetic subspace $\operatorname{span} \{f_{(G,\kappa)}(x) : x > 0\}$ equals $\mathcal{S}$ for every $\kappa$ (true, for example, when every connected component of $G$ is strongly connected). Then for every $x_0 \in \mathbb{R}^n_{>0}$ the map

$$\Psi\colon (x_0 + \mathcal{S})_{>0} \times \mathcal{F}_{\mathrm{disg}}(G) \to \mathcal{K}_{\mathrm{disg}}(G), \qquad \Psi(x,\beta) = \big(\beta_{y\to y'}\, x^{-y}\big)_{y \to y' \in E},$$

is a homeomorphism. Consequently $\mathcal{K}_{\mathrm{disg}}(G)$ is a contractible manifold with boundary of dimension $\dim \mathcal{S} + \dim \mathcal{F}_{\mathrm{disg}}(G)$.

## Depends on

- [Complex-balanced concentrations](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Horn-Jackson: the positive equilibria](../complex-balancing-and-the-deficiency-zero-theore/positive-equilibria-eq.md)

## Expansion

If $x$ is the equilibrium of $(G,\kappa)$ in the class of $x_0$, then $\beta_{y\to y'} = \kappa_{y \to y'} x^{y}$ is the reaction flux at that equilibrium, and $\kappa$ is disguised toric exactly when this flux is a disguised vertex-balanced flux; $\Psi$ inverts the passage from rate constants to equilibrium fluxes. Uniqueness of the equilibrium in each class (Birch-type uniqueness for the realizing vertex-balanced system) makes the inverse a well-defined map, and the implicit function theorem, using the kinetic-subspace hypothesis, shows it is continuous. Since $\mathcal{F}_{\mathrm{disg}}(G)$ is a polyhedral cone intersected with the open orthant, it is contractible, and so is the product. The practical consequence is a computational split: the hard quantifier elimination defining $\mathcal{K}_{\mathrm{disg}}(G)$ reduces to a linear program for the flux cone plus a simpler elimination.

## Sources

- Balázs Boros, Gheorghe Craciun, Oskar Henriksson, Jiaxin Jin, "A flux-based approach for analyzing the disguised toric locus of reaction networks", *Advances in Applied Mathematics* 182 (2027), 103160, Definitions 2.8, 2.13 and 4.3, Theorem 2.14, Theorem 5.3 and Corollary 5.4 (Theorem A), <https://doi.org/10.1016/j.aam.2026.103160> (preprint arXiv:2510.03621).
