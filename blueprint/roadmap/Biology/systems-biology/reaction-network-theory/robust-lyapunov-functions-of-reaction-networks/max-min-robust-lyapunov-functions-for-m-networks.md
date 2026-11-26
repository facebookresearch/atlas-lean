# Max-min robust Lyapunov functions for M-networks

Consider a reaction network with species $X_1, \dots, X_n$, reactions $R_1, \dots, R_\nu$, reactant and product stoichiometric matrices $A, B$, and stoichiometry matrix $\Gamma = B - A \in \mathbb{R}^{n \times \nu}$, with dynamics $\dot x = \Gamma R(x)$ on $\bar{\mathbb{R}}_+^n$. Kinetics $R$ are **admissible** if each $R_j$ is $C^1$, vanishes when any of its reactants is zero, is nondecreasing in each of its reactants and independent of non-reactants, and strictly increasing in its reactants on the open orthant; mass action and Michaelis–Menten kinetics are special cases. Assume the network is non-autocatalytic and has a positive vector in $\ker \Gamma$.

Split the reactions into reversible pairs $R_j \rightleftharpoons R_{-j}$, $j = 1, \dots, \nu_1$, and irreversible reactions $R_{\nu_1+1}, \dots, R_{\tilde\nu}$, and let $\tilde\Gamma$ be the stoichiometry matrix of the **irreversible subnetwork** consisting of the forward reactions $R_1, \dots, R_{\nu_1}$ and the irreversible ones. The network is an **M-network** if the forward directions can be chosen so that $\ker \tilde\Gamma$ is one-dimensional, spanned by $w = (w_1, \dots, w_{\tilde\nu})$.

**Theorem.** Let the network be an M-network whose irreversible subnetwork satisfies:
1. each species is a reactant of exactly one reaction, and
2. every product of a forward reaction $R_j$ ($j \le \nu_1$) is a product of no other reaction.

Then, with the list of scaled net rates

$$\mathcal{R}(x) = \Big\{ \tfrac{1}{w_1}(R_1 - R_{-1}), \dots, \tfrac{1}{w_{\nu_1}}(R_{\nu_1} - R_{-\nu_1}),\ \tfrac{1}{w_{\nu_1+1}} R_{\nu_1+1}, \dots, \tfrac{1}{w_{\tilde\nu}} R_{\tilde\nu} \Big\},$$

the function

$$V(x) = \max \mathcal{R}(x) - \min \mathcal{R}(x)$$

is a convex piecewise-linear robust Lyapunov function, for every admissible kinetics.

## Expansion

At steady state the scaled net fluxes of an M-network must all be equal, since the flux vector lies on the line spanned by $w$; $V$ measures the spread between the fastest and slowest scaled reactions and vanishes exactly on the steady-state set. The two graphical conditions guarantee that when a reaction attains the maximum (or minimum), the concentrations of its reactants are being depleted (or replenished) by the neighboring reactions, so by monotonicity of admissible kinetics the extreme rates move toward each other; the sign of $\dot V$ is read off the reaction graph without knowing the rate laws. Examples covered include simple, cooperative, competitive and three-body binding with inflow and outflow, transcription, and enzymatic activation cycles; for conservative M-networks a graphical LaSalle argument then yields global convergence to a unique steady state in each stoichiometric class.

## Depends on

- [Robust Lyapunov functions as common Lyapunov functions of rank-one systems](robust-lyapunov-functions-as-common-lyapunov-functions-of-rank-one-systems.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- M. Ali Al-Radhawi, D. Angeli, E. D. Sontag, "A computational framework for a Lyapunov-enabled analysis of biochemical reaction networks", PLoS Computational Biology 16(2) (2020) e1007681, Results (Eq 7, "Basic biochemical examples") and Methods ("Graphical criteria for the construction of Max-Min RLFs", Theorem 4, Remark 2), <https://doi.org/10.1371/journal.pcbi.1007681>, PMCID PMC7058358.
