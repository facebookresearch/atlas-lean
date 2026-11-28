# The Marcus–Hush–Chidsey rate saturates at large overpotential

In the uniform-density-of-states Marcus–Hush–Chidsey model, the oxidation rate is strictly increasing in the overpotential and tends to the finite limit $A\sqrt{4\pi\lambda k_BT}$ as $\eta\to\infty$: there is no inverted region at a metal electrode in this model.

For the [Marcus–Hush–Chidsey oxidation rate](marcus-hush-chidsey-rate.md) with $A,\lambda,k_BT>0$:

1. $k_{\mathrm{ox}}$ is continuous and strictly increasing on $\mathbb R$;
2. $\displaystyle\lim_{\eta\to+\infty}k_{\mathrm{ox}}(\eta)=A\sqrt{4\pi\lambda k_BT}$ and $\displaystyle\lim_{\eta\to-\infty}k_{\mathrm{ox}}(\eta)=0$;
3. $0<k_{\mathrm{ox}}(\eta)<A\sqrt{4\pi\lambda k_BT}$ for every $\eta$.

By reciprocity the reduction rate $k_{\mathrm{red}}(\eta)=k_{\mathrm{ox}}(-\eta)$ increases to the same limit as
$\eta\to-\infty$. In the dimensionless form of Zeng et al. ($x$ and $\lambda$ in units of $k_BT$, $\eta$ in units of
$k_BT/e$) the rate $k_{\mathrm{ox}}/(Ak_BT)$ tends to $2\sqrt{\pi\lambda}$.

## Context

Research-level electrode kinetics. A Tafel plot approaching a reaction-limited current, rather than the unbounded Butler–Volmer exponential or the Marcus maximum, is what Chidsey observed for redox-active monolayers and what this model explains.

## Depends on

- [Marcus–Hush–Chidsey rate at a metal electrode](marcus-hush-chidsey-rate.md)

## Proof depends on

- [Dominated convergence theorem for nonnegative functions](../../../MeasureTheory/integration/dominated-convergence-theorem/tendsto-lintegral-of-dominated-convergence.md)
- [Gaussian integral as a lower Lebesgue integral](../../../Probability/linear-models-multivariate/student-s-t-and-snedecor-s-f-distributions/lintegral-exp-neg-mul-sq.md)
- [Detailed balance and reciprocity of Marcus–Hush–Chidsey rates](marcus-hush-chidsey-detailed-balance.md)

## Expansion

Substituting $y=x+e\eta$ gives $k_{\mathrm{ox}}(\eta)=A\int G(y)\,\varphi(y-e\eta)\,dy$ with $G(y)=e^{-(y-\lambda)^2/(4\lambda k_BT)}$ and $\varphi(u)=1/(1+e^{u/k_BT})$ strictly decreasing from $1$ to $0$. The integrands are nonnegative, so the integrals are lower Lebesgue integrals; they are dominated by $G$, whose integral is $\sqrt{4\pi\lambda k_BT}$ by the Gaussian integral with $b=1/(4\lambda k_BT)$. Dominated convergence gives continuity and the two limits. For $\eta_1<\eta_2$, $k_{\mathrm{ox}}(\eta_2)-k_{\mathrm{ox}}(\eta_1)$ and $A\sqrt{4\pi\lambda k_BT}-k_{\mathrm{ox}}(\eta)$ are integrals of positive continuous functions, hence positive. Zeng et al. state the saturation in Sec. II; their large-$\lambda$ approximation Eq. (9) has the same limit but is not used in this proof.

## Sources

- Y. Zeng, R. Smith, P. Bai and M. Z. Bazant, Simple formula for Marcus–Hush–Chidsey kinetics, *Journal of Electroanalytical Chemistry* 735 (2014), 77–83; numbers from arXiv:1407.5370v1, Sec. II (discussion of Figs. 1–2: no inverted region, constant reaction-limited current), Eqs. (4)–(6), and Sec. III B, Eq. (9). [arXiv:1407.5370v1](https://arxiv.org/abs/1407.5370v1); [doi:10.1016/j.jelechem.2014.09.038](https://doi.org/10.1016/j.jelechem.2014.09.038)
