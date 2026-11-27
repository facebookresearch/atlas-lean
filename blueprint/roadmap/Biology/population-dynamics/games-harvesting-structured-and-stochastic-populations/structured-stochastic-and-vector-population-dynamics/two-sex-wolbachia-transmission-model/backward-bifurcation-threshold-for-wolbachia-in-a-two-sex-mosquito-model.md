# Backward-bifurcation threshold for Wolbachia establishment in a two-sex mosquito model

**Model.** Aquatic-stage mosquitoes $A_u, A_w$ (uninfected, Wolbachia-infected), unmated females $F_u, F_w$, mated females $F_{pu}$ (uninfected, fertile), $F_{pw}$ (infected) and $F_{ps}$ (uninfected female mated with an infected male, sterile by cytoplasmic incompatibility), and males $M_u, M_w$ evolve by

$$ \dot A_u = \eta_u F_{pu} + v_u \eta_w F_{pw} - (\mu_a + \psi) A_u, \qquad \dot A_w = v_w \eta_w F_{pw} - (\mu_a + \psi) A_w, $$

$$ \dot F_u = b_f \psi A_u - (\sigma + \mu_{fu}) F_u, \quad \dot F_w = b_f \psi A_w - (\sigma + \mu_{fw}) F_w, \quad \dot F_{pu} = \sigma m_u F_u - \mu_{fu} F_{pu}, \quad \dot F_{pw} = \sigma F_w - \mu_{fw} F_{pw}, $$

$$ \dot M_u = b_m \psi A_u - \mu_{mu} M_u, \qquad \dot M_w = b_m \psi A_w - \mu_{mw} M_w, \qquad \dot F_{ps} = \sigma m_w F_u - \mu_{fw} F_{ps}, $$

where $m_u = M_u/(M_u + M_w)$, $m_w = 1 - m_u$, the oviposition rates are $\eta_{u,w} = \phi_{u,w}(1 - (A_u + A_w)/K_a)$, $v_w \in [0,1]$ is the maternal transmission efficiency, $v_u = 1 - v_w$, $\psi$ is the development rate and $b_f + b_m = 1$.

**Threshold quantities.** The next-generation numbers of uninfected and infected eggs per egg and the basic reproduction number of Wolbachia are

$$ \mathbb{G}_{0u} = b_f \frac{\psi}{\mu_a + \psi} \frac{\sigma}{\sigma + \mu_{fu}} \frac{\phi_u}{\mu_{fu}}, \qquad \mathbb{G}_{0w} = v_w b_f \frac{\psi}{\mu_a + \psi} \frac{\sigma}{\sigma + \mu_{fw}} \frac{\phi_w}{\mu_{fw}}, \qquad \mathcal{R}_0 = \frac{\mathbb{G}_{0w}}{\mathbb{G}_{0u}} = v_w \frac{\mu_{fu} \phi_w (\sigma + \mu_{fu})}{\mu_{fw} \phi_u (\sigma + \mu_{fw})}. $$

With $\mathbb{G}_{0u} > 1$ the Wolbachia-free equilibrium has $A_u^0 = K_a(1 - 1/\mathbb{G}_{0u})$. Endemic equilibria (with $\mu_{mw} = \mu_{mu}$) are determined by the infected-to-uninfected aquatic ratio $r = A_w/A_u > 0$ solving

$$ \frac{v_u}{v_w} r^2 + \Bigl( \frac{v_u}{v_w} - 1 \Bigr) r + \frac{1 - \mathcal{R}_0}{\mathcal{R}_0} = 0. $$

For perfect transmission ($v_w = 1$) the unique root is $r^* = (1 - \mathcal{R}_0)/\mathcal{R}_0$ for $0 < \mathcal{R}_0 < 1$; for $1/2 < v_w < 1$ the roots are $r^\pm = \frac{1}{2 v_u}\bigl( 2 v_w - 1 \pm \sqrt{1 - 4 v_u v_w / \mathcal{R}_0} \bigr)$, giving no endemic equilibrium for $\mathcal{R}_0 < 4 v_u v_w$, two ($EE^+$, $EE^-$) for $4 v_u v_w < \mathcal{R}_0 < 1$, and only $EE^+$ for $\mathcal{R}_0 \ge 1$.

**Theorem (stability).** The system has a unique solution remaining in the biologically feasible domain. The Wolbachia-free equilibrium is locally asymptotically stable if $\mathbb{G}_{0u} > 1$ and $\mathcal{R}_0 < 1$. The complete-infection equilibrium (possible only for $v_w = 1$) is locally asymptotically stable if $\mathbb{G}_{0w} > 1$. For $v_w = 1$, the endemic equilibrium $EE^*$ (with $\mathcal{R}_0 < 1$, $\mathbb{G}_{0w} > 1$) is unstable; for $v_w < 1$, $EE^+$ is locally asymptotically stable when $\mathcal{R}_0 > 4 v_u v_w$ and $EE^-$ is unstable when $4 v_u v_w < \mathcal{R}_0 < 1$.

Hence there is a backward bifurcation: since infection lowers fitness ($\mathcal{R}_0 < 1$), small introductions die out, but releases pushing the infected fraction above the unstable $EE^-$ (or $EE^*$) establish a stable Wolbachia population.

## Expansion

The infected compartments are $(A_w, F_w, F_{pw}, M_w)$; new infections enter only through $v_w \eta_w F_{pw}$, so $J_{\mathcal{F}} J_{\mathcal{V}}^{-1}$ at the Wolbachia-free state has the single nonzero eigenvalue $\mathbb{G}_{0w}/\mathbb{G}_{0u}$, because the oviposition factor $1 - A_u^0/K_a$ equals $1/\mathbb{G}_{0u}$. At an endemic state, the aquatic carrying-capacity factor and the proportions of infected males feed into the mating fractions, and eliminating all variables except $r$ gives the quadratic. Stability follows from the Jacobian at each equilibrium: at the complete-infection state the uninfected subsystem is suppressed because every uninfected female mates with an infected male and becomes sterile, while at $EE^-$ the Jacobian has a positive eigenvalue, making it the release threshold separating the basins of the Wolbachia-free and endemic states.

## Sources

- Zhuolin Qu, Ling Xue, James M. Hyman, "Modeling the Transmission of Wolbachia in Mosquitoes for Controlling Mosquito-Borne Diseases", SIAM Journal on Applied Mathematics 78 (2018), 826–852, <https://doi.org/10.1137/17m1130800>. Published version of arXiv:1708.03025, cited next; locators there refer to the arXiv version.
- Zhuolin Qu, Ling Xue, James M. Hyman, "Modeling the transmission of Wolbachia in mosquitoes for controlling mosquito-borne diseases", arXiv (2017). Section 2 (model, forward invariance theorem), Section 3 (equilibria, $\mathbb{G}_{0u}$, $\mathbb{G}_{0w}$, $\mathcal{R}_0$, endemic equilibria), Section 4 (stability theorems). <https://doi.org/10.48550/arXiv.1708.03025>
