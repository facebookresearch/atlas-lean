# Splicing kinetics and RNA velocity

**Model.** For one gene in one cell, let $u(t)$ and $s(t)$ be the amounts of unspliced and spliced RNA, with constant transcription rate $\alpha \ge 0$, splicing rate $\beta > 0$ and degradation rate $\gamma > 0$:

$$\dot u = \alpha - \beta u, \qquad \dot s = \beta u - \gamma s, \qquad u(0) = u_0,\ s(0) = s_0 .$$

The **RNA velocity** of the gene is $\dot s = \beta u - \gamma s$.

**Solution.** For $\beta \ne \gamma$,

$$u(t) = u_0 e^{-\beta t} + \frac{\alpha}{\beta}\bigl(1 - e^{-\beta t}\bigr),$$

$$s(t) = s_0 e^{-\gamma t} + \frac{\alpha}{\gamma}\bigl(1 - e^{-\gamma t}\bigr) + \frac{\alpha - \beta u_0}{\gamma - \beta}\bigl(e^{-\gamma t} - e^{-\beta t}\bigr),$$

and for $\beta = \gamma$,

$$s(t) = s_0 e^{-\gamma t} + \frac{\alpha}{\gamma}\bigl(1 - e^{-\gamma t}\bigr) + (\beta u_0 - \alpha)\, t\, e^{-\gamma t}.$$

The steady state is $u^* = \alpha/\beta$, $s^* = \alpha/\gamma$, so on the steady-state line $u^* = \tilde\gamma\, s^*$ with $\tilde\gamma = \gamma/\beta$; a steady-state regression of $u$ on $s$ identifies only the ratio $\tilde\gamma$.

**Labelling experiments.** If labelled species follow the same equations with transcription rate $\rho\alpha$ ($\rho$ a labelling-efficiency factor):

- *pulse* (kinetics) experiments start from $u_l(0) = s_l(0) = 0$, giving $u_l(t) = \frac{\rho\alpha}{\beta}(1 - e^{-\beta t})$ and $s_l(t) = \frac{\rho\alpha}{\gamma}(1 - e^{-\gamma t}) + \frac{\rho\alpha}{\gamma - \beta}(e^{-\gamma t} - e^{-\beta t})$;
- *chase* (degradation) experiments have no new labelled synthesis ($\alpha = 0$ for labelled species), giving $u_l(t) = u_{l,0} e^{-\beta t}$ and $s_l(t) = s_{l,0} e^{-\gamma t} - \frac{\beta u_{l,0}}{\gamma - \beta}(e^{-\gamma t} - e^{-\beta t})$.

Fitting these curves at several time points estimates $\beta, \gamma$ (and $\alpha$) on an absolute time scale. When the time resolution cannot resolve splicing, an absolute $\gamma$ obtained from labelling combined with the steady-state ratio $\tilde\gamma$ gives $\beta = \gamma/\tilde\gamma$. In a pulse experiment of duration $t$ with $\rho = 1$, the per-cell transcription rate is $\alpha = \beta u_l/(1 - e^{-\beta t})$, so the unspliced velocity is $\dot u = \beta u_l/(1 - e^{-\beta t}) - \beta u$.

## Depends on

- [Metabolic-labelling kinetics of new and total RNA](metabolic-labelling-kinetics-of-new-and-total-rna.md)

## Expansion

The first equation is a linear ODE with constant forcing. Substituting $u(t)$ into the second and solving with the integrating factor $e^{\gamma t}$ gives the stated $s(t)$; differentiating confirms $\dot s(0) = \beta u_0 - \gamma s_0$. Letting $\beta \to \gamma$ in $(e^{-\gamma t} - e^{-\beta t})/(\gamma - \beta)$ gives $-t e^{-\gamma t}$, which yields the resonant formula. The pulse and chase formulas are the special initial conditions and forcing of the general solution.

## Sources

- X. Qiu, Y. Zhang, J. D. Martin-Rufino, C. Weng, S. Hosseinzadeh, D. Yang, A. N. Pogson, M. Y. Hein, K. H. J. Min, L. Wang, et al., *Mapping transcriptomic vector fields of single cells*, Cell 185 (2022), <https://doi.org/10.1016/j.cell.2021.12.045>, PMCID PMC9332140. STAR Methods, "Estimating absolute RNA velocity for metabolic labeling-based scRNA-seq experiments across various labeling strategies" (Model 3 solutions, including the case $\beta = \gamma$), "Kinetics (pulse) experiment" and "Degradation (chase) experiments" (pulse and chase solutions, $\beta = \gamma/\tilde\gamma$).
- G. La Manno, R. Soldatov, A. Zeisel, et al., *RNA velocity of single cells*, Nature 560 (2018), 494–498, <https://doi.org/10.1038/s41586-018-0414-6>.
