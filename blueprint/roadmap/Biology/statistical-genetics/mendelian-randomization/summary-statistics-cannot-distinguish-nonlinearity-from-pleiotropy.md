# Summary statistics cannot distinguish nonlinearity from pleiotropy

**Setting.** In two-sample Mendelian randomization each variant $j$ contributes only its exposure and outcome regression coefficients $(\gamma_{A,j}, \gamma_{Y,j})$ (and allele frequencies), and per-variant ratios $\theta_j = \gamma_{Y,j}/\gamma_{A,j}$ are pooled. Under a nonlinear dose-response, each $\theta_j$ is a variant-specific weighted average of the slope of the dose-response curve, so the $\theta_j$ can differ even when every instrument is valid.

**Proposition 1 (observational equivalence).** Any collection of summary statistics $\{(\gamma_{A,j}, \gamma_{Y,j})\}$ with $\gamma_{A,j} \ne 0$, with any allele frequencies, is generated exactly by both of the following data-generating processes:

1. valid instruments (no direct effect on the outcome) satisfying the additive-density condition $f(a \mid u, z) = c(a,u) + \Lambda(a,z)$, with nonnegative variant weights and a nonlinear dose-response; and
2. a linear constant-effect dose-response with a direct (pleiotropic) effect of each variant on the outcome.

Consequently no function of the summary statistics, including Cochran's $Q$, the MR-Egger intercept, funnel-plot asymmetry, MR-PRESSO and leave-one-out analyses, can separate pleiotropy from nonlinearity; InSIDE, plurality and zero-modal-pleiotropy assumptions are, when nonlinearity is possible, untestable assumptions about the first stage.

## Expansion

The proof is constructive. For process 2, take $A = \sum_j \gamma_{A,j} G_j + U + \eta$ and $Y = \theta A + \sum_j \alpha_j G_j + U + \varepsilon$ with independent variants and errors; then $\operatorname{cov}(G_j, Y)/\operatorname{var}(G_j) = \theta\gamma_{A,j} + \alpha_j$, which matches $\gamma_{Y,j}$ with $\alpha_j = \gamma_{Y,j} - \theta\gamma_{A,j}$ for any $\theta$.

For process 1, fix disjoint dose intervals $I_1, \dots, I_L$ and let a latent selector route each individual's exposure: with probability $\pi_j$ the exposure is drawn from a location family supported in $I_j$ whose location shifts with $G_j$ by $\delta_j$, with probability $\pi_u(U)$ from a confounder-driven density, and otherwise from a fixed density. The resulting conditional density is additive in each variant and the confounder, so the weighted-average-derivative representation holds, and each variant's weight $g_j(a) = \pi_j \operatorname{cov}\{G_j, S_j(a \mid G_j)\}$ is nonnegative and supported in $I_j$, with $\pi_j\delta_j = \gamma_{A,j}$. Choosing $Y = h(A) + U + \varepsilon$ with $h' = \theta_j$ on $I_j$ makes the Wald ratio of variant $j$ equal to $\theta_j$, matching $\gamma_{Y,j}$; if the $\theta_j$ differ, $h$ is nonlinear. The two processes differ only in the conditional distribution of exposure given genotype, which summary data do not report. Associations of each variant with a few transforms of the exposure (powers, splines or threshold indicators $\mathbf{1}(A > a)$) would reveal the weights and break the equivalence.

## Depends on

- [Wald ratio as a weighted average derivative under a nonlinear dose-response](wald-ratio-as-weighted-average-derivative-under-nonlinear-dose-response.md)

## Sources

- Eric J. Tchetgen Tchetgen, "What does two-sample Mendelian randomization estimate when the exposure-outcome relationship is nonlinear?," arXiv 2026. Section 5, Proposition 1; Appendix D (constructive proof). <https://doi.org/10.48550/arXiv.2610.05134>
