# Geometric-mean fitness criterion on two-colored graphs

**Theorem.** Under the hypotheses of the [fixation formula on properly two-colored biregular graphs](fixation-probability-on-properly-two-colored-biregular-graphs.md) (birth-death Moran process, proper two-coloring, green degree $k_G$, red degree $k_R$, fitness $a_G, a_R$ for $A$ and $b_G, b_R$ for $B$),

$$\rho_A > \frac{1}{N} > \rho_B \iff \rho_A > \rho_B \iff a_G a_R > b_G b_R .$$

Moreover $\rho_A = 1/N$ (neutral fixation) if and only if $a_G a_R = b_G b_R$. Thus selection favors $A$ exactly when its geometric-mean fitness over the two colors, $g_A = \sqrt{a_G a_R}$, exceeds that of $B$, $g_B = \sqrt{b_G b_R}$, irrespective of $N_G$, $N_R$ and the degrees; arithmetic mean fitness does not decide the outcome.

## Depends on

- [Fixation probability on properly two-colored biregular graphs](fixation-probability-on-properly-two-colored-biregular-graphs.md)

## Expansion

The identities $a_R(a_Gk_R + b_Rk_G) - b_R(a_Rk_G + b_Gk_R) = k_R(a_Ga_R - b_Gb_R)$ and $a_G(a_Rk_G + b_Gk_R) - b_G(a_Gk_R + b_Rk_G) = k_G(a_Ga_R - b_Gb_R)$ show that $1 - \zeta_G$ and $1 - \zeta_R$ share the sign of $a_Ga_R - b_Gb_R$. Setting $\rho_A = 1/N$ in the fixation formula gives $f(\zeta_G,\zeta_R) = 0$ with $f(x,y) = N_G(1-x) + N_R(1-y) - 1 + x^{N_G}y^{N_R}$ and $f(1,1) = 0$. If $(\zeta_G,\zeta_R) \ne (1,1)$, Rolle's theorem on the segment from $(1,1)$ to $(\zeta_G,\zeta_R)$ gives a point where the directional derivative vanishes, but since both coordinates of $(1-\zeta_G, 1-\zeta_R)$ have the same sign this derivative cannot vanish. Hence neutrality holds exactly when $\zeta_G = \zeta_R = 1$, i.e. $a_Ga_R = b_Gb_R$, and monotonicity in the fitness values gives the strict inequalities.

## Sources

- K. Kaveh, A. McAvoy, K. Chatterjee, M. A. Nowak, "The Moran process on 2-chromatic graphs", PLoS Computational Biology 16 (2020) e1008402, Theorem 2, Eq. (4), Appendix Eqs. (26)–(28), <https://doi.org/10.1371/journal.pcbi.1008402>, PMCID PMC7671562.
