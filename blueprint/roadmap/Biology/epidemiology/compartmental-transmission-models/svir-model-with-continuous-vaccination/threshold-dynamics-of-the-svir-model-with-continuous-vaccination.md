# Threshold dynamics of the SVIR model with continuous vaccination

**Model.** Let $S,V,I,R\ge0$ be the fractions of susceptibles, vaccinees (individuals in the vaccination process), infected and recovered, with $S+V+I+R=1$. With transmission rates $\beta$ (to susceptibles) and $\beta_1$ (to vaccinees), recovery rate $\gamma$, immunization rate $\gamma_1$ of vaccinees, vaccination rate $\alpha\ge0$ and birth-death rate $\mu$ (all of $\beta,\beta_1,\gamma,\gamma_1,\mu>0$),

$$S'=\mu-\beta SI-(\alpha+\mu)S,\qquad V'=\alpha S-\beta_1VI-(\gamma_1+\mu)V,\qquad I'=\beta SI+\beta_1VI-(\gamma+\mu)I,\qquad R'=\gamma_1V+\gamma I-\mu R .$$

The total population is constant, so the dynamics reduce to $(S,V,I)$. The disease-free equilibrium is

$$E_0=\Big(\frac{\mu}{\mu+\alpha},\;\frac{\alpha\mu}{(\mu+\gamma_1)(\mu+\alpha)},\;0\Big),$$

and the control reproduction number is

$$R_0^C=\frac{\mu\beta}{(\mu+\alpha)(\mu+\gamma)}+\frac{\alpha\mu\beta_1}{(\mu+\gamma_1)(\mu+\alpha)(\mu+\gamma)} .$$

**Theorem (local behavior).** $E_0$ always exists; it is locally asymptotically stable if $R_0^C<1$ and unstable if $R_0^C>1$. The system has a unique positive (endemic) equilibrium

$$E_+=\Big(\frac{\mu}{\mu+\alpha+\beta I_+},\;\frac{\alpha\mu}{(\mu+\alpha+\beta I_+)(\mu+\gamma_1+\beta_1I_+)},\;I_+\Big)$$

if and only if $R_0^C>1$, where $I_+>0$ is the positive root of a quadratic whose coefficients depend on the parameters, and $E_+$ is locally asymptotically stable whenever it exists.

**Theorem (global behavior).** If $R_0^C\le1$, $E_0$ is globally asymptotically stable; if $R_0^C>1$, $E_+$ is globally asymptotically stable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

$R_0^C$ is the next-generation number at $E_0$: a single infective lasts $1/(\mu+\gamma)$ on average and infects susceptibles at rate $\beta S^0$ and vaccinees at rate $\beta_1V^0$, with $(S^0,V^0)$ the disease-free coordinates; the two terms are these contributions. It decreases in $\alpha$ when $\beta_1<\beta$, so faster vaccination lowers the threshold. Setting $I'=0$ with $I>0$ and substituting the equilibrium expressions of $S$ and $V$ in terms of $I$ leaves a quadratic equation for $I_+$, which has a unique positive root exactly when $R_0^C>1$. Local stability is read off the Jacobian at each equilibrium; the global statements are taken from the original analysis of the model and are summarized, not reproved, in the cited source.

## Sources

- Xianning Liu, Yasuhiro Takeuchi, Shingo Iwami, "SVIR epidemic models with vaccination strategies", Journal of Theoretical Biology 253 (2008), 1–11, <https://doi.org/10.1016/j.jtbi.2007.10.014>. The model with continuous vaccination, its equilibria, $R_0^C$ and the local and global stability theorems.
- Alessandro Ramponi, M. Elisabetta Tessitore, "The economic cost of social distancing during a pandemic: an optimal control approach in the SVIR model", Decisions in Economics and Finance 48 (2025), 485–516, <https://doi.org/10.1007/s10203-023-00406-0>. Published version of arXiv:2208.04908, cited next; locators there refer to the arXiv version.
- A. Ramponi and M. E. Tessitore, "The economic cost of social distancing during a pandemic: an optimal control approach in the SVIR model", arXiv:2208.04908 (2022), Section 2 (model, equilibria, $R_0^C$, Theorems 1 and 2, summarizing the analysis of Liu, Takeuchi and Iwami), <https://doi.org/10.48550/arXiv.2208.04908>.
