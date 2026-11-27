# Fixation probability on properly two-colored biregular graphs

**Setting.** Let $G$ be a connected undirected graph whose $N = N_G + N_R$ nodes carry a *proper* two-coloring (no edge joins two nodes of the same color), with every green node of degree $k_G$ and every red node of degree $k_R$; counting edges gives $N_G k_G = N_R k_R$. Two types $A$ and $B$ occupy the nodes, and a type's fitness depends on the color of its node through the color-to-fitness matrix

$$\begin{array}{c|cc} & G & R \\ \hline A & a_G & a_R \\ B & b_G & b_R \end{array}, \qquad a_G, a_R, b_G, b_R > 0.$$

In the birth-death Moran process, at each step one individual is chosen to reproduce with probability proportional to its fitness, and its offspring replaces a uniformly random neighbor.

**Theorem.** Let

$$\zeta_G = \frac{b_R(a_R k_G + b_G k_R)}{a_R(a_G k_R + b_R k_G)}, \qquad \zeta_R = \frac{b_G(a_G k_R + b_R k_G)}{a_G(a_R k_G + b_G k_R)}.$$

The fixation probability of a single $A$ mutant placed uniformly at random in a population of $B$ is

$$\rho_A = \frac{1 - \frac{1}{N}\big(N_G\,\zeta_G + N_R\,\zeta_R\big)}{1 - \zeta_G^{N_G}\,\zeta_R^{N_R}},$$

and $\rho_B$ is obtained by exchanging the roles of $(a_G, a_R)$ and $(b_G, b_R)$. In particular, $\rho_A$ depends on the graph only through $(N_G, N_R, k_G, k_R)$, so every properly two-colored regular graph ($k_G = k_R$, hence $N_G = N_R$) has the same fixation probabilities as the complete bipartite graph $K_{N/2,N/2}$, independently of the degree.

## Depends on

- [Isothermal theorem for evolutionary graph dynamics](../../../isothermal-theorem-for-evolutionary-graph-dynami/README.md)

## Expansion

Seek constants $\zeta_1,\dots,\zeta_N$ such that $\zeta^{X_n} = \prod_i \zeta_i^{X_{n,i}}$ is a martingale for the state $X_n \in \{0,1\}^N$ (1 marks an $A$ node). The martingale condition is a pseudo-Boolean identity in $x$, so its linear and quadratic coefficients must vanish separately. With a proper two-coloring and color-constant degrees one can take $\zeta_i = \zeta_G$ on green and $\zeta_i = \zeta_R$ on red nodes; the linear equations then force the stated values of $\zeta_G, \zeta_R$, and the quadratic equations hold automatically. Optional stopping gives $\zeta^{x} = (1 - \rho_A(x)) + \rho_A(x)\,\zeta_G^{N_G}\zeta_R^{N_R}$, i.e. $\rho_A(x) = (1 - \zeta^x)/(1 - \zeta_G^{N_G}\zeta_R^{N_R})$, and averaging over a uniformly placed mutant (green with probability $N_G/N$) yields the formula. Example: on the star with a red center, $N_G = k_R = N-1$ and $N_R = k_G = 1$.

## Sources

- K. Kaveh, A. McAvoy, K. Chatterjee, M. A. Nowak, "The Moran process on 2-chromatic graphs", PLoS Computational Biology 16 (2020) e1008402, Eqs. (1)–(2), Theorem 1, Appendix Eqs. (11)–(25), <https://doi.org/10.1371/journal.pcbi.1008402>, PMCID PMC7671562.
