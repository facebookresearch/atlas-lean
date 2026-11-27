# Scaled kinetic flux profiling model and steady-state identifiability

**Graph model.** A pathway with $N$ metabolites and $R$ constant fluxes is a connected directed weighted graph whose edges split into labeled inputs $\mathcal E_{\mathcal L}$, unlabeled inputs $\mathcal E_{\mathcal U}$, outputs $\mathcal E_{\mathcal V}$ and internal edges $\mathcal E_{\mathcal W}$, every metabolite reachable from a labeled input. With $\mathbf W$ the weighted adjacency matrix of internal fluxes ($w_{ij}$ from $i$ to $j$), $\mathbf X^{\mathcal T}$ the diagonal matrix of total concentrations and $\hat{\mathbf b}$ the unlabeled inflows, the unlabeled concentrations after the switch to labeled nutrient at $t = 0$ satisfy the linear system

$$\dot{\mathbf X}^{\mathcal U} = \hat{\mathbf A}\mathbf X^{\mathcal U} + \hat{\mathbf b}, \qquad \mathbf X^{\mathcal U}(0) = \mathbf X^{\mathcal T}\mathbf 1,$$

where $\hat{\mathbf A}$ collects $\mathbf W^{T}(\mathbf X^{\mathcal T})^{-1}$ minus the outflow terms; at metabolic steady state total inflow equals total outflow, $\mathbf F_{\mathrm{in}} = \mathbf F_{\mathrm{out}} = \mathbf F$ (diagonal).

**Scaled model.** In the measured proportions unlabeled $\bar{\mathbf X} = (\mathbf X^{\mathcal T})^{-1}\mathbf X^{\mathcal U}$, with flux-ratio parameters $\boldsymbol\alpha = \mathbf F^{-1}\hat{\mathbf b}$ ($\alpha_i$ is the fraction of flux into metabolite $i$ coming from unlabeled external input), $\mathbf B = \mathbf F^{-1}\mathbf W^{T}$ ($\beta_{ij}$ the fraction of flux into $i$ coming from $j$) and turnover rates $\mathbf K = (\mathbf X^{\mathcal T})^{-1}\mathbf F$,

$$\dot{\bar{\mathbf X}} = \mathbf K(\mathbf B - \mathbf I)\bar{\mathbf X} + \mathbf K\boldsymbol\alpha, \qquad \bar{\mathbf X}(0) = \mathbf 1.$$

**Theorem (parameter count).** The flux-balance constraints allow the original system to be rewritten in terms of $R - N$ independent flux parameters. The scaled model has $R - |\mathcal E_{\mathcal V}|$ parameters ($N$ turnover rates plus flux ratios), which equals the minimum $R - N$ when every metabolite has an outflow.

**Theorem (steady state).** The scaled model has the unique steady state $\bar{\mathbf X}^{ss} = (\mathbf I - \mathbf B)^{-1}\boldsymbol\alpha$, which depends only on the flux ratios $\boldsymbol\alpha, \mathbf B$ and not on the turnover rates $\mathbf K$. Hence turnover rates are never identifiable from steady-state labeling alone, and flux ratios are recoverable from steady state only when the map $(\boldsymbol\alpha, \mathbf B) \mapsto \bar{\mathbf X}^{ss}$ is injective; for an arborescence (tree-shaped pathway) it is, since each non-root node satisfies $\bar x_i^{ss} = 1 - (1 - \alpha_i)(1 - \bar x_j^{ss})$ with $j$ its unique upstream metabolite.

## Expansion

Labeled nutrient enters only through $\mathcal E_{\mathcal L}$, so the unlabeled fraction of each pool relaxes from $1$ to a steady value set by how much of its inflow is ultimately unlabeled; $\mathbf K$ only sets the speed. Since $\mathbf K$ is invertible it drops out of the steady-state equation $(\mathbf B - \mathbf I)\bar{\mathbf X} + \boldsymbol\alpha = 0$, and $\mathbf I - \mathbf B$ is invertible because every metabolite is connected to an input. A reversible two-metabolite example has three flux ratios but only two steady-state observations, so transient data are needed; Bayesian estimation on simulated time courses quantifies how many time points suffice.

## Sources

- B. Guppy, C. Mitchell and E. Taylor, "Parameter Estimation and Identifiability in Kinetic Flux Profiling Models of Metabolism", *Bulletin of Mathematical Biology* 87(1) (2024), 7, Section 2 (scaled model), Theorems 1 and 2 and Section 3, <https://doi.org/10.1007/s11538-024-01386-x> (preprint arXiv:2407.08844).