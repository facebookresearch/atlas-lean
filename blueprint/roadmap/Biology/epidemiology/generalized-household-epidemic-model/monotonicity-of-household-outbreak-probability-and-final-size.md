# Monotonicity of outbreak probability and final size in household size and global mixing

**Model.** In the household epidemic $\mathcal{E}_{n,h}(X_G,X_L)$ ($n$ households of size $h$; each infective makes $X_G$ uniformly random global contacts and $X_L$ uniformly random contacts within its household), the modified model $\mathcal{E}_{n,h}(X_G,X_L,p)$ independently converts each local contact into a global one with probability $p \in [0,1]$; equivalently its contact vector is $(X_G + Y, X_L - Y)$ with $Y \sim \mathrm{MixBin}(X_L,p)$, and $p = 1$ is homogeneous mixing. Let $\pi^{(h,p)}$ be the limiting ($n \to \infty$) probability of a major outbreak from one initial case and $z^{(h,p)}$ the limiting final fraction infected in a major outbreak. Write $\mu_G, \mu_L$ for the means of $X_G, X_L$, $\sigma_L^2 = \operatorname{Var}X_L$, $\alpha = \mu_G + \mu_L$, $f_{X_L}$ for the pgf of $X_L$, and $z_{\mathrm{hom}}(\alpha)$ for the positive root of $1 - z = e^{-\alpha z}$.

**Theorem.**
1. For every $(X_G,X_L)$, $\pi^{(h,p)}$ is monotonically increasing in both $h$ and $p$.
2. If $\log f_{X_L}(s)$ is convex on $[0,1]$, then $z^{(h,p)}$ is monotonically increasing in $h$ and $p$, for any $X_G$ (dependent on $X_L$ or not).
3. Suppose $\alpha > 1$. If $\sigma_L^2 \ge \mu_L$, then $z^{(h,p)}$ is strictly increasing in $p$ near $p = 1$. If $\sigma_L^2 < \mu_L$, let $z^*(\mu_L,\sigma_L^2) = 1 - \dfrac{\mu_L - \sigma_L^2}{3\mu_L^2}$; then $z^{(h,p)}$ is strictly increasing in $p$ near $1$ when $z_{\mathrm{hom}}(\alpha) < z^*$ and strictly decreasing when $z_{\mathrm{hom}}(\alpha) > z^*$.
4. If $\alpha > 1$, then $z^{(h,p)} \to z_{\mathrm{hom}}(\alpha)$ as $h \to \infty$ for every $p \in [0,1]$.

## Depends on

- [Central limit theorem for the final size of a household epidemic with general contact numbers](final-size-clt-for-household-epidemics-with-general-contact-numbers.md)

## Expansion

Local contacts are partly wasted on already-infected household members, so making contacts global (larger $p$) or spreading local contacts over more members (larger $h$) can only help the early branching process, which gives part 1 by a coupling of the household branching processes. For the final size the effect is subtler: in a major outbreak a local contact may reach a household member that global infection would have missed. Log-convexity of the local-contact pgf (true for mixed Poisson $X_L$, e.g. the classical model) restores monotonicity, but for under-dispersed local contacts (e.g. a fixed number) and large outbreaks, mixing more globally can strictly decrease the final size, the threshold being $z_{\mathrm{hom}}(\alpha) = z^*$. In very large households local contacts behave like global ones, giving the homogeneous limit.

## Sources

- F. Ball, T. Britton, P. Neal, "Household epidemic models revisited", arXiv:2505.17890 (2025), Theorems 2.2–2.5 (Section 2), with proofs in Sections 5, 8 and 9, <https://doi.org/10.48550/arXiv.2505.17890>.
