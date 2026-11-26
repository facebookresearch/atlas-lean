# State-specific mediated and direct genetic effects on single-cell expression trajectories

**Model.** Donors $i = 1, \dots, n$ have genotype dosage $Z_i$; each of their cells $c$ has a mediator gene expression $X_{ic}$ (a candidate cis gene), an outcome gene expression $Y_{ic}$ (a distal gene), and a coarse annotation $S_{ic} \in \{0,1\}$. Each cell carries a latent state $t_{ic} \in [0,1]$ with $t_{ic} \mid S_{ic} \sim \mathrm{Unif}([0, 0.5])$ if $S_{ic} = 0$ and $\mathrm{Unif}([0.5, 1])$ if $S_{ic} = 1$, and

$$ X_{ic} = g_i(t_{ic}) + \epsilon_{ic}, \quad Y_{ic} = h_i(t_{ic}) + \delta_{ic}, \qquad g_i(t) = \phi(t)^\top \boldsymbol\alpha_i, \quad h_i(t) = \phi(t)^\top \boldsymbol\beta_i, $$

with $\phi$ a cubic B-spline basis of dimension $K$ and independent Gaussian errors with donor-specific variances. The donor-level mediation hierarchy is

$$ \boldsymbol\alpha_i = \boldsymbol\alpha_0 + A Z_i + \boldsymbol\eta_i, \qquad \boldsymbol\beta_i = \boldsymbol\beta_0 + C Z_i + B \boldsymbol\alpha_i + \boldsymbol\xi_i, $$

with independent Gaussian deviations $\boldsymbol\eta_i, \boldsymbol\xi_i$ (diagonal covariances) and $B = \operatorname{diag}(b_1, \dots, b_K)$. Equivalently, with Gram matrix $G_\phi = \int_0^1 \phi \phi^\top$ and kernel $\zeta(s,t) = \phi(s)^\top G_\phi^{-1} B^\top \phi(t)$, $h_i(t) = \phi(t)^\top(\boldsymbol\beta_0 + C Z_i) + \int_0^1 \zeta(s,t) g_i(s)\, ds + \phi(t)^\top \boldsymbol\xi_i$, so the outcome at a state depends on the whole mediator trajectory.

**Effect functions.** For an exposure contrast $\Delta z = z_1 - z_0$,

$$ \mathrm{ME}(t) = \phi(t)^\top B A\, \Delta z, \qquad \mathrm{DE}(t) = \phi(t)^\top C\, \Delta z, \qquad \mathrm{TE}(t) = \phi(t)^\top (BA + C)\, \Delta z = \mu_Y(t \mid z_1) - \mu_Y(t \mid z_0), $$

so $\mathrm{TE} = \mathrm{ME} + \mathrm{DE}$ at every state, and under diagonal $B$, $\mathrm{ME}(t) = \sum_k \phi_k(t) b_k a_k \Delta z$. Integrating over the state domain gives scalar summaries.

**Proposition 1 (causal interpretation).** If the potential mediator and outcome trajectories follow the corresponding structural equations on a common cellular-state coordinate, then under the identification assumptions (A1)-(A8) (among them consistency, no interference between donors, positivity of the exposure levels and mediator support, exposure exchangeability $\{\boldsymbol\alpha_i(z'), \boldsymbol\beta_i(z, \mathbf{a})\} \perp Z_i$, and mediator-outcome exchangeability $\boldsymbol\beta_i(z, \mathbf{a}) \perp \boldsymbol\alpha_i(z')$), the model-based effect functions equal the functional natural effects: the natural indirect effect is $\mathrm{NIE}(t; z_1, z_0) = \mathrm{ME}(t; z_1, z_0)$, the natural direct effect is $\mathrm{NDE}(t; z_1, z_0) = \mathrm{DE}(t; z_1, z_0)$, and the natural total effect is $\mathrm{NTE}(t; z_1, z_0) = \mathrm{TE}(t; z_1, z_0)$.

## Expansion

Substituting the mediator equation into the outcome equation gives $\boldsymbol\beta_i = \boldsymbol\beta_0 + B\boldsymbol\alpha_0 + (BA + C) Z_i + B\boldsymbol\eta_i + \boldsymbol\xi_i$, and taking expectations over the donor deviations gives the conditional mean trajectories, whose difference splits into the path through the mediator coefficients ($BA$) and the remaining path ($C$). With linear structural equations, the cross-world counterfactual $h_i(t; z_1, g_i(\cdot; z_0))$ appearing in natural effects has expectation obtained by plugging the mediator coefficients at $z_0$ into the outcome map at $z_1$, which yields exactly $\phi(t)^\top C \Delta z$ for the direct part and $\phi(t)^\top BA \Delta z$ for the indirect part. Joint Bayesian inference over latent states, trajectories and coefficients propagates state uncertainty into the effect curves; averaging expression within donors before analysis can change the split between mediated and direct components even when the total association is preserved, because it mixes cells at different states.

## Sources

- Zehua Li, Yang Ni, Weixuan Zhu, "Bayesian Latent Functional Mediation Analysis with Application to Population-Scale Single-Cell Data", arXiv (2026). Section 2 (model, latent states, donor-level hierarchy, effect functions, Proposition 1) and Supplementary Section A (assumptions and derivations). <https://doi.org/10.48550/arXiv.2611.33714>
