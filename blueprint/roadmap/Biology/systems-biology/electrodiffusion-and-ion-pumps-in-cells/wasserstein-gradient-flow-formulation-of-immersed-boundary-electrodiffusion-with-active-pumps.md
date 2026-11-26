# Wasserstein gradient-flow formulation of immersed-boundary electrodiffusion with active ion pumps

**Model.** Let $\Omega \subset \mathbb{R}^2$ be a bounded $C^2$ domain or the flat torus. A cell membrane is a closed curve $\mathbf{X} : \mathbb{S}^1 \to \Omega$ immersed in a Stokes fluid of velocity $\mathbf{u}$. Ion species $i = 1,\dots,N$ (valences $z_i$, diffusivities $D_i$) have densities $c_i$ with fixed masses $M_i$ (the admissible set $\mathcal{K}_{\mathbf{M}}$), and the electric potential $\varphi[\mathbf{c}]$ solves Poisson's equation with permittivity $\epsilon$. The membrane enters through smoothed Eulerian kernels of width $w > 0$: a passive chemical-barrier potential $\psi^{\mathrm{passive}}_{i,w}(\cdot;\mathbf{X})$ and a non-conservative active pumping potential $\psi^{\mathrm{active}}_{i,w}(\cdot;\mathbf{X})$ that models the ATP-driven $3{:}2$ $\mathrm{Na}^+/\mathrm{K}^+$ exchanger. The passive free energy is

$$
\mathcal{E}_w(\mathbf{c},\mathbf{X}) = \sum_{i=1}^N k_BT\int_\Omega c_i(\log c_i - 1) + \frac{\epsilon}{2}\int_\Omega|\nabla\varphi[\mathbf{c}]|^2 + \sum_{i=1}^N\int_\Omega c_i\,\psi^{\mathrm{passive}}_{i,w}(\cdot;\mathbf{X}) + \frac{K}{2}\int_{\mathbb{S}^1}|\partial_s\mathbf{X}|^2\,ds ,
$$

whose first variation in $c_i$ is the electrochemical potential $\mu_i = k_BT\log c_i + qz_i\varphi + \psi^{\mathrm{passive}}_{i,w}$. The ions follow the Poisson–Nernst–Planck equations with pump drift (and advection by $\mathbf{u}$),

$$ \partial_t c_i = \nabla\cdot\Big(D_i\nabla c_i + \frac{D_i}{k_BT}c_i\nabla\big(qz_i\varphi + \psi^{\mathrm{passive}}_{i,w} + \psi^{\mathrm{active}}_{i,w}\big)\Big), $$

so the passive part is the $W_2$ gradient flow of $\mathcal{E}_w$ with mobility $D_i/k_BT$, and the pump adds a non-gradient push.

**Theorem (global weak existence).** Let $\mathbf{c}_0 \in \mathcal{K}_{\mathbf{M}}$ have finite entropy $\sum_i\int c_{i,0}\log c_{i,0} < \infty$ and let $\mathbf{X}_0 \in H^3(\mathbb{S}^1;\Omega)$ be a closed, non-self-intersecting $C^2$ curve. For every $w > 0$ and $T > 0$ there is a global weak solution $(\mathbf{c},\mathbf{X},\mathbf{u},\varphi)$ on $[0,T]$ with $\mathbf{c} \in C([0,T];W_2) \cap L^1$, $c_i > 0$ a.e., $\mathbf{X} \in C([0,T];H^2(\mathbb{S}^1)) \cap L^\infty(0,T;H^3(\mathbb{S}^1))$, $\mathbf{u} \in L^2(0,T;H^1_0\cap H^3)$ and $\varphi \in L^\infty(0,T;W^{2,p})$ for all $p < \infty$, satisfying the continuity equations in the distributional sense.

**Energy balance.** Along such a solution, the passive free energy changes at the rate

$$ \frac{d}{dt}\mathcal{E}_w = -\sum_{i=1}^N\int_\Omega\frac{D_i}{k_BT}c_i|\nabla\mu_i|^2 + (\text{power injected by the pumps}), $$

so the electrodiffusive dissipation is nonnegative and the active pumps are the only source of free energy, which is why the long-time state is a non-equilibrium steady state rather than an equilibrium.

## Expansion

Existence uses a split-step Jordan–Kinderlehrer–Otto scheme: each time step $\tau$ minimizes $\mathcal{E}_w + \tfrac{1}{2\tau}\sum_i W_2^2(\cdot, c_i^{k})$ for the passive part, then transports the minimizer along the active pushing field and updates the membrane by the Stokes flow. The discrete energy inequality gives uniform entropy bounds, Calderón–Zygmund estimates bound the Poisson drift $\nabla\varphi$ in $L^\infty$, and Stokes regularity propagates $H^3$ regularity of the interface. Tightness of the piecewise geodesic interpolants in $W_2$ lets $\tau \to 0$. The paper further claims exponential $W_2$ contraction to a unique steady state once $w$ exceeds a Bakry–Émery curvature threshold, and studies the sharp-interface limit $w \to 0$ and the small-Debye-length limit.

## Sources

- Pilhwa Lee, "Immersed Boundary Electrodiffusion in the Wasserstein Gradient Flow Formalism: Global Well-Posedness, Non-Equilibrium Thermodynamics, and Singular Asymptotics", arXiv:2610.40942 (2026), Section 1.3, Theorems 1.1 (global weak existence) and 1.3 (Rayleighian power balance and NESS stability); Section 2.3 (free energy and first variations); Section 3 (split-step JKO scheme), <https://doi.org/10.48550/arXiv.2610.40942>.
