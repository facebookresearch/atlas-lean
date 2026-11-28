# Equilibrium bounds for networks with as many reactions as species and rank one less

**Setting.** A reaction network with $n$ species and $m$ reactions $a_j \to b_j$ ($a_j, b_j \in \mathbb{Z}^n_{\ge 0}$) has stoichiometric matrix $\Gamma \in \mathbb{Z}^{n\times m}$ with columns $b_j-a_j$ and rank $r$; it is called an $(n,m,r)$ network. Under mass action with rate constants $\kappa \in \mathbb{R}^m_{>0}$ the dynamics are $\dot x = \Gamma\,(\kappa \circ x^{A})$, where $x^{A}$ is the vector of monomials $x^{a_j}$. Positive equilibria lie in stoichiometric classes $(x_0 + \operatorname{im}\Gamma)\cap\mathbb{R}^n_{>0}$; an equilibrium is *nondegenerate* if the Jacobian restricted to $\operatorname{im}\Gamma$ is nonsingular. The *sources* are the distinct reactant complexes $a_j$. The network is *dynamically nontrivial* if its positive flux cone $\ker\Gamma\cap\mathbb{R}^m_{>0}$ is nonempty.

**Theorem ($(n,n,n-1)$ networks).** Consider an $(n,n,n-1)$ mass-action network (as many reactions as species, stoichiometric subspace of codimension one).

1. It admits at most $n$ positive nondegenerate equilibria on any stoichiometric class.
2. If its stoichiometric classes are bounded, it admits at most two positive nondegenerate equilibria on any stoichiometric class.
3. If the network is quadratic (every source has total degree at most $2$), it admits at most two positive nondegenerate equilibria on each stoichiometric class, the smallest $n$ for which two are attained is $n=3$, and the bound drops to one if $\mathbf{1}\in\operatorname{im}A$ and there is a nonzero $\omega\in\ker\Gamma^{\top}\cap\mathbb{R}^n_{\ge 0}$.

Here $A$ is the $m\times n$ matrix whose rows are the sources.

## Expansion

The general result behind items 1–2 covers $(n,m,n-1)$ networks that are not overdetermined with respect to their finest flux-cone partition $\mathcal{P}_f$ and satisfy $n\le m\le n+p_f-1$: such networks are toric (the positive equilibrium set has a monomial parameterisation $\mu\mapsto c(\kappa)\circ\mu^{\widehat Q}$), so equilibria on a stoichiometric class solve $Z\big(c(\kappa)\circ\mu^{\widehat Q}\big)=K$ for a single conservation law $Z$. The normalised volume of the convex hull of the relevant exponent rows and the origin bounds the number of nondegenerate solutions by $n$; a nonnegative conservation law reduces the count to two. In the quadratic case the exponent matrix $\widehat Q$ can be chosen with entries in $\{-1,0,1,2\}$, which gives the sharper bounds.

## Sources

- M. Banaji, E. Feliu, "Positive equilibria in mass action networks: geometry and bounds", *Journal of Mathematical Biology* 93(3) (2026), 37, Theorem 4.16, Corollary 4.17 and Corollary 5.13, <https://doi.org/10.1007/s00285-026-02429-8> (preprint arXiv:2409.06877).
