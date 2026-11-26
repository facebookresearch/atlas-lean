# Regularity of binary and endotactic mass-action systems

**Setting.** A reaction network $\mathcal R$ on $d$ species is a finite set of reactions $y\to y'$ between complexes $y,y'\in\mathbb Z^d_{\ge0}$, with propensities $\lambda_{y\to y'}$. The *stochastic reaction system* is the continuous-time Markov chain on $\mathbb N^d$ jumping by $y'-y$ at rate $\lambda_{y\to y'}(x)$; the *deterministic reaction system* is the ODE $\dot x=\sum\lambda_{y\to y'}(x)(y'-y)$ on $\mathbb R^d_{\ge0}$. A reaction system is **regular** if the Markov chain is non-explosive (finitely many jumps in finite time almost surely), respectively if every ODE solution exists for all $t\ge0$. The *molecularity* of $y\to y'$ is $\|y\|_1$; a network is *bimolecular* (second order under mass action) if all molecularities are at most $2$, and *binary* if moreover every product $y'$ has $\|y'\|_1\le2$. For $u\in\mathbb R^d_{>0}$ let $\mathcal R_{u,+}=\{y\to y':u\cdot y'>u\cdot y\}$ be the reactions increasing along $u$.

**Theorems 3.2 and 3.3 (linear growth along a direction).** If for some $u\in\mathbb R^d_{>0}$
$$\sup_{y\to y'\in\mathcal R_{u,+}}\ \sup_{x\ne0}\ \frac{\lambda_{y\to y'}(x)}{\|x\|_1}<\infty,$$
then the stochastic system is regular (with $x\in\mathbb N^d$), and likewise the deterministic system (with $x\in\mathbb R^d_{\ge0}$). In particular the system is regular if $\mathcal R_{u,+}=\emptyset$ for some positive $u$.

**Theorem 4.1 (second-order mass-action systems).** (a) Every binary mass-action system is regular. (b) Every second-order $\mathbf 1$-endotactic mass-action system is regular; in particular every second-order lower-endotactic, and every second-order endotactic, mass-action system is regular.

**Theorem 4.3 and Corollary 4.4 (positive recurrence).** A second-order weakly reversible stochastic mass-action system is positive recurrent if and only if every communicating class carries a stationary distribution. More generally, for a binary or $\mathbf 1$-endotactic second-order stochastic mass-action system, positive recurrence on a closed communicating class is equivalent to the existence of a stationary distribution there, and each closed class carries at most one stationary distribution (Theorem 4.2).

## Expansion

Theorems 3.2 and 3.3 use the linear Lyapunov function $V(x)=u\cdot x$: reactions decreasing $V$ only help, and reactions increasing it have at most linearly growing rates, so $\mathcal LV\le C_1V+C_2$, which rules out explosion by a standard Foster-Lyapunov criterion. For a binary network, any reaction that increases the total molecule count must have a reactant of molecularity at most one (since products have at most two molecules), so with $u=\mathbf 1$ its mass-action rate is at most linear; $\mathbf 1$-endotacticity similarly forbids second-order reactions from pointing outward in the $\mathbf 1$ direction. Once explosion is excluded, a stationary distribution on an irreducible class forces positive recurrence. The criteria apply to SIRS epidemic, Lotka-Volterra, glycolysis, Brusselator, circadian-clock and immunological network models.

## Sources

- C. Xu, "On the regularity of reaction systems", arXiv preprint (2024), Theorem 3.2, Theorem 3.3, Theorems 4.1-4.3, Corollary 4.4, <https://doi.org/10.48550/arXiv.2409.05340>.
