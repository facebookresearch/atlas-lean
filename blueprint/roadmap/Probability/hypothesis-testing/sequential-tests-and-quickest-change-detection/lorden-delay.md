# Lorden's worst-case detection delay

Let $P_0$ and $P_1$ be probability measures on a measurable space $\mathcal{X}$, $\mathsf{P}_\nu$ the [change-point law](change-point-law.md) with change at observation $\nu$ (independent observations, $X_1, \dots, X_{\nu-1} \sim P_0$ and $X_\nu, X_{\nu+1}, \dots \sim P_1$), and $\mathcal{F}_n = \sigma(X_1, \dots, X_n)$. Lorden's worst-case detection delay of an alarm time $T$ is

$$\overline{\mathrm{WADD}}(T) = \sup_{\nu \ge 1}\ \sup_{F \in \mathcal{F}_{\nu-1},\ \mathsf{P}_\nu(F) > 0} \frac{\mathsf{E}_\nu\big[(T - \nu + 1)^+ ; F\big]}{\mathsf{P}_\nu(F)} \in [0, \infty],$$

with $(T - \nu + 1)^+ = \infty$ when $T = \infty$. This is $\sup_{\nu \ge 1} \operatorname{ess\,sup} \mathsf{E}_\nu[(T - \nu + 1)^+ \mid X_1, \dots, X_{\nu-1}]$ (Lorden's convention, as in Lai 2001, §3) written without conditional expectations.

The two forms agree: for $Y \ge 0$ and a σ-algebra $\mathcal F$, $\operatorname{ess\,sup} \mathsf E[Y \mid \mathcal F] = \sup \{ \mathsf E[Y; F]/P(F) : F \in \mathcal F,\ P(F) > 0 \}$, because $\mathsf E[Y; F] = \mathsf E[\mathsf E[Y \mid \mathcal F]; F]$. Lorden's convention counts a delay of $1$ when the alarm is raised at the change point; Veeravalli and Banerjee drop the $+1$ (their footnote 3), Lai keeps it.

## Sources

- T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica 11 (2001) 303–408, §3, p. 316.
- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §IV, equation (51) and footnote 3.
