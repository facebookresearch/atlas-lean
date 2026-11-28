# Lifting nondegenerate multistationarity to networks with intermediates

Let $G$ be a mass-action reaction network with *core species* $X_1,\dots,X_n$ and a set $\mathcal{I} = \{U_1,\dots,U_p\}$ of *intermediate species*: each $U_i$ appears only as a complex consisting of one copy of itself, and is produced from and consumed to core complexes through chains of intermediates. The *reduced network* $G_{red}$ is obtained by deleting the intermediates and collapsing every reaction path $y \to U_{i_1} \to \dots \to y'$ between core complexes into a single reaction $y \to y'$; conversely $G$ is an *extension* of $G_{red}$.

At steady state the intermediates are monomial combinations of the core concentrations, $u_i = \sum_{y} \mu_{i,y}(\kappa)\, x^{y}$ with positive rational functions $\mu_{i,y}$ of the rate constants $\kappa$ of $G$, and substituting into the core equations yields mass-action dynamics on $G_{red}$ with rate constants

$$\tau(\kappa)_{y\to y'} = \kappa_{y \to y'} + \sum_{j=1}^p \kappa_{U_j \to y'}\, \mu_{j,y}(\kappa),$$

defining a map $T\colon \mathbb{R}^{\#\mathcal{R}_G}_{>0} \to \mathbb{R}^{\#\mathcal{R}_{G_{red}}}_{>0}$, $\kappa \mapsto \tau(\kappa)$. A steady state $x^*$ is *nondegenerate* if $\ker J f(x^*) \cap S = \{0\}$, with $S$ the stoichiometric subspace.

**Theorem.** Let $\tau^0 \in \operatorname{im} T$ and let $\mathcal{F}_{\tau^0} = T^{-1}(\tau^0)$.

1. For every $\varepsilon > 0$ the set $\mathcal{F}_{\tau^0,\varepsilon} = \{\kappa \in \mathcal{F}_{\tau^0} : \mu_{i,y}(\kappa) < \varepsilon \text{ for all } i, y\}$ is nonempty and open in the fiber.
2. Fix a stoichiometric compatibility class of $G_{red}$ given by conservation laws $\ell_1(x) = c_1, \dots, \ell_d(x) = c_d$. If $G_{red}$ with rate constants $\tau^0$ has $m$ nondegenerate positive steady states in that class, there is $\varepsilon_0 > 0$ such that for every $\kappa \in \mathcal{F}_{\tau^0,\varepsilon}$ with $0 < \varepsilon < \varepsilon_0$ the network $G$ has at least $m$ nondegenerate positive steady states in the class $\bar\ell_1(x,u) = c_1, \dots, \bar\ell_d(x,u) = c_d$, where $\bar\ell_k$ are the conservation laws of $G$ obtained from $\ell_k$ by adding the intermediates.
3. If every intermediate is added in one of the local shapes $y \rightleftharpoons U \to y'$, $y \to U \to y'$ or $y \rightleftharpoons U$, the same conclusion holds on the nonempty sets $\{\kappa \in \mathcal{F}_{\tau^0} : \kappa_{U_i \to y'} > M\}$ for all sufficiently large $M$: fast consumption of intermediates also lifts multistationarity.

## Depends on

- [Network transformations transfer injectivity and multistationarity](../../chemical-reaction-network-theory/network-transformations-transfer-injectivity-and-multistationarity.md)

## Expansion

When all $\mu_{i,y}$ are small, the intermediates carry a vanishing fraction of the conserved totals, so the steady-state equations of $G$ restricted to a class are a small perturbation of those of $G_{red}$ (with $u = \varphi(x)$ substituted). Nondegeneracy means the Jacobian of the reduced system restricted to the class is invertible, so the implicit function theorem continues each of the $m$ reduced steady states to a nondegenerate steady state of $G$; positivity is preserved for small perturbations. The fiber $\mathcal{F}_{\tau^0}$ is used so that the effective reduced rate constants stay equal to $\tau^0$ while the intermediate concentrations are driven to zero. The result refines Feliu-Wiuf's theorem that adding intermediates preserves multistationarity by identifying explicit open regions of parameter space where it happens.

## Sources

- Alicia Dickenstein, Magalí Giaroli, Mercedes Pérez Millán, Rick Rischter, "Multistationarity questions in reduced vs extended biochemical networks", *Journal of Mathematical Biology* 89(2) (2024), 18, Definitions 2.3 and 2.9, Theorems 2.14 and 2.15, <https://doi.org/10.1007/s00285-024-02115-7> (preprint arXiv:2310.02455).
