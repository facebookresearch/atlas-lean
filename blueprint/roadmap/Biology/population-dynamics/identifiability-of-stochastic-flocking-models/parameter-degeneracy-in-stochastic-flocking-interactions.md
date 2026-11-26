# Parameter degeneracy in stochastic flocking interactions

**Setting.** Agents move at constant speed $v_0$ in the plane. Either the heading obeys $d\theta_i=\omega_i^{\mathrm{soc}}dt+\sigma_\theta dW_i$ (overdamped), or the turning rate obeys $d\omega_i=-(\omega_i-\omega_i^{\mathrm{soc}})\tau^{-1}dt+\sigma_\omega dW_i$ (inertial), where the social turning rate $\omega_i^{\mathrm{soc}}$ combines separation, cohesion and alignment interactions with Voronoi neighbors; parameters are fitted by Euler-Maruyama quasi-maximum likelihood.

**Structural degeneracy (two agents).** In a model whose social turning rate for agent 1 is

$$\omega_1^{\mathrm{soc}}=e_1^{\perp}\cdot\Big[(k^{\mathrm{coh}}-k^{\mathrm{sep}})\frac{x_2-x_1}{\|x_2-x_1\|}+k^{\mathrm{alg}}\frac{v_2-v_1}{\|v_2-v_1\|}\Big],$$

the cohesion and separation gains enter only through $k^{\mathrm{coh}}-k^{\mathrm{sep}}$, so the likelihood is exactly invariant along the lines $k^{\mathrm{coh}}-k^{\mathrm{sep}}=\mathrm{const}$: the model is completely degenerate for $N=2$ and the minimum Hessian eigenvalue stagnates. The degeneracy disappears for groups of more than two agents.

**Dynamical degeneracy (ordered state).** In a model whose positional interaction switches from separation to cohesion through $\tanh\big(m(\|x_j-x_i\|-d^{\mathrm{eq}})\big)$ at an equilibrium spacing $d^{\mathrm{eq}}$, spacings concentrate near $d^{\mathrm{eq}}$ in the ordered state and linearization gives

$$\omega_i^{\mathrm{soc}}\approx\frac{1}{|\mathcal{N}_i|}\sum_{j\in\mathcal{N}_i}\Big[k^{\mathrm{alg}}\sin(\theta_j-\theta_i)+\hat k^{\mathrm{pos}}\,m\,(\|x_j-x_i\|-d^{\mathrm{eq}})\sin\phi_{ij}\Big],$$

where $\hat k^{\mathrm{pos}}$ and $m$ enter only through their product. The only information separating them is the cubic term $-\hat k^{\mathrm{pos}}m^3(\|x_j-x_i\|-d^{\mathrm{eq}})^3/3$, so estimates spread along $\hat k^{\mathrm{pos}}m=\mathrm{const}$ even though the model has no exact redundancy: identifiability depends on the dynamical regime, not only on model structure.

## Depends on

- [Minimum Hessian eigenvalue growth diagnoses identifiability of SDE models](minimum-hessian-eigenvalue-growth-diagnoses-sde-identifiability.md)

## Expansion

An exact redundancy gives a direction in log-parameter space along which every likelihood increment is flat, the completely degenerate case of the eigenvalue theorem, so longer observation never helps; the remedy is reparameterization. A regime-induced near-redundancy instead leaves a direction informed only by fluctuations of order $(\|x_j-x_i\|-d^{\mathrm{eq}})m$, which are small in the ordered state; observing transients with spacing deviations comparable to $1/m$ could restore identifiability. In simulations (50 trajectories per model, 24 Hz sampling, 5 min of data), the estimates lie along the predicted degenerate manifolds in both cases, while models with null interactions show linear eigenvalue growth.

## Sources

- Natsuki Kurita, Hiroshi Kori, "Diagnosing parameter unidentifiability in stochastic dynamics with an application to flocking models", arXiv:2610.38615 (2026), Section 2.2 (flocking models), Section 4.4 (physical origin of unidentifiability) and Section 4.1 (numerical configuration), <https://doi.org/10.48550/arXiv.2610.38615>
