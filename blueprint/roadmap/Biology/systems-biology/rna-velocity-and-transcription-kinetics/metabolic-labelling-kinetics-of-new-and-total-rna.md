# Metabolic-labelling kinetics of new and total RNA

**Model.** For one gene in one cell, let $r(t)$ be total RNA and $l(t)$ the RNA labelled since the start $t = 0$ of a labelling pulse (new RNA). With synthesis rate $\alpha \ge 0$, degradation rate $\gamma > 0$ and labelling-efficiency factor $\rho \in (0, 1]$,

$$\dot l = \rho\alpha - \gamma l, \qquad \dot r = \alpha - \gamma r, \qquad l(0) = 0,\ r(0) = r_0 .$$

**Solution.**

$$l(t) = \frac{\rho\alpha}{\gamma}\bigl(1 - e^{-\gamma t}\bigr), \qquad r(t) = r_0 e^{-\gamma t} + \frac{\alpha}{\gamma}\bigl(1 - e^{-\gamma t}\bigr).$$

**One-shot estimator.** If total RNA is at steady state, $r = \alpha/\gamma$, then for a labelling time $t$

$$l = k\, r, \qquad k = \rho\bigl(1 - e^{-\gamma t}\bigr),$$

so $k$ is the zero-intercept slope of $l$ against $r$ across cells. With labelled RNA corrected so that $\rho = 1$,

$$\gamma = -\frac{1}{t}\ln(1 - k), \qquad \alpha = \frac{\gamma\, l}{1 - e^{-\gamma t}} = \frac{\gamma}{k}\, l,$$

and the velocity of total RNA in absolute time units is

$$\dot r = \alpha - \gamma r = \frac{\gamma}{k}\, l - \gamma r .$$

The transcription rate is thus estimated cell by cell from that cell's new RNA, rather than assumed constant within a cell state.

**Two-step estimator for pulse series.** With labelling times $t_1 < \dots < t_J$, the slopes $k(t_j) = 1 - e^{-\gamma t_j}$ increase towards $1$, and

$$-\ln\bigl(1 - k(t_j)\bigr) = \gamma\, t_j ,$$

so $\gamma$ is the slope of a second zero-intercept regression of $-\ln(1 - \hat k_j)$ on $t_j$.

**Chase.** After a long labelling period followed by wash-out, labelled RNA decays as $l(t) = l_0 e^{-\gamma t}$.

## Expansion

Both equations are linear with constant forcing and decay rate $\gamma$; the integrating factor $e^{\gamma t}$ gives the solutions. At steady state $\alpha = \gamma r$, so $l/r = \rho(1 - e^{-\gamma t})$ independently of $\alpha$, which is why all cells sampled at one labelling time lie on a line through the origin whose slope encodes $\gamma$. Inverting $k = 1 - e^{-\gamma t}$ gives $\gamma$, and inverting $l(t)$ gives $\alpha$; both are absolute rates because the labelling time $t$ is an experimental clock. If $\rho < 1$ is ignored, $k$ underestimates $1 - e^{-\gamma t}$ and $\gamma$ is biased downward.

## Sources

- X. Qiu, Y. Zhang, J. D. Martin-Rufino, C. Weng, S. Hosseinzadeh, D. Yang, A. N. Pogson, M. Y. Hein, K. H. J. Min, L. Wang, et al., *Mapping transcriptomic vector fields of single cells*, Cell 185 (2022), <https://doi.org/10.1016/j.cell.2021.12.045>, PMCID PMC9332140. STAR Methods, "Estimating absolute RNA velocity for metabolic labeling-based scRNA-seq experiments across various labeling strategies" (Model 2 and its solutions), "One-shot experiment" ($l = kr$, $\gamma = -\ln(1-k)/t$, total-RNA velocity) and "Kinetics (pulse) experiment" (two-step approach).
- F. Erhard, M. A. P. Baptista, T. Krammer, et al., *scSLAM-seq reveals core features of transcription dynamics in single cells*, Nature 571 (2019), 419–423, <https://doi.org/10.1038/s41586-019-1369-y>.
