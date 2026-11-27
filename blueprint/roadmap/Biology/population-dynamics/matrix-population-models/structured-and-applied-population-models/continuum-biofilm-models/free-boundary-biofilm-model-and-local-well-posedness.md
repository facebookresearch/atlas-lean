# Free-boundary biofilm model and its local well-posedness

**Model.** A biofilm occupies $0 \le z \le L(t)$ above a substratum at $z = 0$. Microbial species $i \in J_f$ (for plasmid transfer: plasmid-free cells, plasmid carriers, conjugation-able donors, inert biomass, and so on) have volume fractions $f_i(z, t) \ge 0$ with $\sum_i f_i = 1$, and dissolved substances $j \in J_S$ (nutrients, metals, antibiotics) have concentrations $S_j(z, t)$. With growth rates $r_{M,i}(f, S)$ and conversion terms $R_i(z, f, S)$ (decay, conjugation, gene expression; possibly nonlocal in $z$) satisfying $\sum_i R_i = 0$, the model is

$$\partial_t f_i + \partial_z (u f_i) = r_{M,i}(f, S) + R_i(z, f, S), \qquad \partial_z u = \sum_{i \in J_f} r_{M,i}(f, S), \quad u(0, t) = 0,$$

$$\partial_t S_j - \partial_z\big(D_{S,j}\, \partial_z S_j\big) = r_{S,j}(f, S), \qquad \dot L(t) = u(L(t), t) - \sigma_d(L(t), t), \quad \sigma_d = \delta L^2,$$

(Equations 1, 2, 23, 27, 28), with initial fractions $f_{i,0}$ on $[0, L_0]$, no-flux conditions for $S_j$ at the substratum and Dirichlet data $S_j^*(t)$ at the free boundary. The growth velocity $u$ is obtained by summing the $f_i$ equations, since $\sum_i f_i \equiv 1$ and conversions do not create volume.

**Theorem 1 (local existence and uniqueness).** Consider the model with zero detachment ($\sigma_d \equiv 0$, so $\dot L = u(L, t)$) and quasi-steady substrates ($-\partial_z(D_{S,j}\,\partial_z S_j) = r_{S,j}(f, S)$ in place of the parabolic equations, the source's Eq. (34)). Write this system in Lagrangian coordinates along the characteristics $z = c(z_0, t)$, $\partial_t c = u(c, t)$, $c(z_0, 0) = z_0 \in [0, L_0]$, with unknowns $c$, $\partial_{z_0} c$, $x_i(z_0, t) = f_i(c(z_0, t), t)$ and $s_j(z_0, t)$. Suppose the initial data $f_{i,0}$ and boundary data $S_j^* > 0$ are continuous, the total growth $G = \sum_i r_{M,i}$ is essentially positive, $L_0$ is small, and all right-hand sides of the transformed system are bounded and Lipschitz in their arguments, with bounds $M$ and Lipschitz constants as in the hypotheses. Then the transformed system, the integral system (A11)–(A14) of the source's Appendix A, has a unique continuous solution $(c, \partial_{z_0} c, x, s)$ on $[0, L_0] \times [0, T]$ for an explicit $T > 0$ depending on $L_0$, the bounds and the admissible deviations from the initial data.

## Expansion

Along characteristics the transport equations become ordinary differential equations in $t$ for each $z_0$, and without detachment the free boundary is simply $L(t) = c(L_0, t)$, which removes the moving domain. The quasi-steady substrate equations are converted to integral equations on the fixed interval. Detachment $\sigma_d = \delta L^2$ and parabolic substrates are used in the source's simulations but are not covered by Theorem 1. The full system then becomes a fixed-point problem $\mathcal{A}(c, \partial_{z_0} c, x, s) = (c, \partial_{z_0} c, x, s)$ on a closed ball of continuous functions around the initial data, and in the weighted sup-norm $\max e^{-\alpha t} |\cdot|$ with $\alpha$ large the Lipschitz hypotheses make $\mathcal{A}$ a contraction; the small time $T$ keeps iterates in the ball. The application in the paper models plasmid conjugation regulated by local recipient density and promoted by trace metals, and shows numerically that contaminants favour plasmid persistence.

## Sources

- J. Vincent, A. Tenore, M. R. Mattei, L. Frunzo, "Modelling plasmid-mediated horizontal gene transfer in biofilms", Bulletin of Mathematical Biology 86 (2024) 63, Equations (1)–(3), (23), (27)–(29), Theorem 1, <https://doi.org/10.1007/s11538-024-01289-x> (PMC11561024).
