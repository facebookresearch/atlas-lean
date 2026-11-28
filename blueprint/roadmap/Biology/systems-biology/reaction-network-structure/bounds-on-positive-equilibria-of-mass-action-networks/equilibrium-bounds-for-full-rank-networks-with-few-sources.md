# Equilibrium bounds for full-rank mass-action networks with few sources

**Setting.** A reaction network with $n$ species and $m$ reactions $a_j \to b_j$ ($a_j, b_j \in \mathbb{Z}^n_{\ge 0}$) has stoichiometric matrix $\Gamma \in \mathbb{Z}^{n\times m}$ with columns $b_j-a_j$ and rank $r$; it is called an $(n,m,r)$ network. Under mass action with rate constants $\kappa \in \mathbb{R}^m_{>0}$ the dynamics are $\dot x = \Gamma\,(\kappa \circ x^{A})$, where $x^{A}$ is the vector of monomials $x^{a_j}$. Positive equilibria lie in stoichiometric classes $(x_0 + \operatorname{im}\Gamma)\cap\mathbb{R}^n_{>0}$; an equilibrium is *nondegenerate* if the Jacobian restricted to $\operatorname{im}\Gamma$ is nonsingular. The *sources* are the distinct reactant complexes $a_j$. The network is *dynamically nontrivial* if its positive flux cone $\ker\Gamma\cap\mathbb{R}^m_{>0}$ is nonempty.

**Theorem (few distinct sources, rank $n$).** Let the network be an $(n,m,n)$ network, i.e. $\Gamma$ has full rank $n$.

1. If it has at most $n+1$ distinct sources, then for every choice of rate constants it has either no positive equilibrium, exactly one positive equilibrium (which is nondegenerate), or a continuum of positive degenerate equilibria.
2. If it is dynamically nontrivial and has $n+2$ distinct sources, then for every choice of rate constants it has at most $n+1$ positive nondegenerate equilibria.

## Expansion

Positive equilibria are solutions of $\kappa\circ x^A \in \ker\Gamma$. Writing a flux $v\in\ker\Gamma\cap\mathbb{R}^m_{>0}$ in coordinates on the flux cone and eliminating $x$ through the monomial relations among sources produces an alternative system, in one-to-one smooth correspondence with the positive equilibria, whose number of variables and monomials is controlled by the number of sources. With $n+1$ sources it is a "fewnomial" system with $k=0$ (no, one, or infinitely many positive solutions); with $n+2$ sources it has $k=1$, and the bound of $n+1$ positive nondegenerate solutions for such systems applies.

## Sources

- M. Banaji, E. Feliu, "Positive equilibria in mass action networks: geometry and bounds", *Journal of Mathematical Biology* 93(3) (2026), 37, Proposition 2.2, Corollary 4.20 and Theorem 4.24, <https://doi.org/10.1007/s00285-026-02429-8> (preprint arXiv:2409.06877).
