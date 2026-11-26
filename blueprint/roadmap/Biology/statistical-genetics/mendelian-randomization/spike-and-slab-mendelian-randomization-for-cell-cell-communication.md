# Spike-and-slab Mendelian randomization for cell–cell communication

Given the identifying working model $Y = \mu + \beta_XX^* + \beta_ZZ^* + \beta_{XZ}X^*\!\circ Z^* + V\alpha_Y + \varepsilon_Y$ for a ligand–receptor–pathway triplet, with $X^* = G\pi_X + V\alpha_X$ and $Z^* = H\pi_Z + V\alpha_Z$ the instrument-based exposure means, MR-CCC is the Bayesian hierarchy:

- exposure models with Zellner $g$-priors, $\pi_X \mid \sigma_X^2 \sim N(0,\sigma_X^2g_G(G^\top G)^{-1})$, $\alpha_X \mid \sigma_X^2 \sim N(0,\sigma_X^2g_V(V^\top V)^{-1})$, $\sigma_X^2 \sim \mathrm{IG}(a_\sigma,b_\sigma)$, and likewise for $(\pi_Z,\alpha_Z,\sigma_Z^2)$;
- a joint spike-and-slab prior on the communication vector $\beta = (\beta_X,\beta_{XZ})$ with design $X_\beta = [X^*\ \ X^*\!\circ Z^*]$,

$$\beta \mid \gamma,\sigma_Y^2 \sim N_2\big(0,\ s_\gamma\sigma_Y^2g_\beta(X_\beta^\top X_\beta)^{-1}\big), \qquad s_1 = 1,\ s_0 = \nu_1 \ll 1, \qquad \gamma \sim \mathrm{Bernoulli}(\rho),\ \rho \sim \mathrm{Beta}(a_\rho,b_\rho);$$

- $g$-priors on the nuisance coefficients $\alpha_Y$, $\beta_Z$, an inverse-gamma prior on $\sigma_Y^2$ and a diffuse normal prior on $\mu$.

All full conditionals are closed form, so a Gibbs sampler alternates: update exposure parameters, recompute $X^*$, $Z^*$ and $X_\beta$, update outcome nuisance parameters, then $\beta \mid \gamma$, $\gamma$ and $\rho$. Evidence for causal signaling is the posterior inclusion probability $\mathrm{PIP} = \Pr(\gamma = 1 \mid \text{data})$, and effect estimates are posterior means of $\beta_X$ and $\beta_{XZ}$.

## Depends on

- [Plug-in identification of receptor-modulated ligand effects](plug-in-identification-of-receptor-modulated-ligand-effects.md)

## Expansion

Sampling the first-stage parameters inside the Gibbs loop propagates instrument uncertainty into $X^*$, $Z^*$ and their product, which a plug-in second stage would ignore. Selecting $(\beta_X,\beta_{XZ})$ jointly asks whether the ligand acts on the pathway at all, either directly or through the receptor-dependent term, and the $g$-prior scaling by $(X_\beta^\top X_\beta)^{-1}$ makes the prior invariant to the scale and correlation of main effect and interaction. In simulations with confounding the PIP controls false discoveries where naive co-expression regression does not, and the interaction term separates receptor-limited signaling (effect growing with receptor abundance) from receptor-independent association.

## Sources

- Bitan Sarkar and Yang Ni, *MR-CCC: Bayesian Mendelian Randomization for Causal Cell–Cell Communication*, arXiv:2604.23917 (2026). <https://doi.org/10.48550/arXiv.2604.23917> Methods, "Bayesian Formulation of MR-CCC" (priors and Gibbs sampler; full conditionals in Supplementary Section S1).
