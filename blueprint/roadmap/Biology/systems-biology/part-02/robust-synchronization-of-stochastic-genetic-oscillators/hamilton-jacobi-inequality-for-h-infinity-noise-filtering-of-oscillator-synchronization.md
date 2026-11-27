# Hamilton–Jacobi inequality for H-infinity noise filtering of oscillator synchronization

**Setting.** Let $N$ cells each carry a genetic oscillator with state $x_i \in \mathbb R^m$, coupled through a matrix $C = (c_{ij})$ (for example via a diffusing quorum-sensing autoinducer), with intrinsic noise driven by independent standard Wiener processes $w_i$ and extrinsic noise $v_i(t)$ entering through matrices $h_i$:

$$dx_i = \Big[f(x_i) + \sum_{j} c_{ij}\,g(x_j) + h_i v_i\Big]dt + \Big[f_W(x_i) + \sum_j c_{ij}\,g_W(x_j)\Big]dw_i .$$

Let $s(t)$ be the synchronized solution, $e_i = x_i - s$, and stack $e = (e_1, \dots, e_N)$, $v = (v_1,\dots,v_N)$, $w = (w_1,\dots,w_N)$. The error obeys

$$de = \big[\mathcal F(x,s) + (C\otimes I_m)\,\mathcal G(x,s) + \mathcal H v\big]dt + \Sigma(x,s)\,dw,$$

where $\mathcal F, \mathcal G$ stack the differences $f(x_i) - f(s)$, $g(x_i) - g(s)$, $\mathcal H = \mathrm{diag}(h_i - h_s)$ and $\Sigma = \mathcal F_W + (C\otimes I_m)\mathcal G_W$ collects the block-diagonal diffusion differences. For a symmetric positive semidefinite weight $R$ and a level $\rho > 0$, the **$H_\infty$ noise-filtering property** is

$$\mathbb E\int_0^{t_f} e^{\top}Re\,dt \ \le\ \mathbb E\,V(e(0)) + \rho^2\,\mathbb E\int_0^{t_f} v^{\top}v\,dt \qquad\text{for all } v .$$

**Proposition.** Suppose $V \in C^2$, $V \ge 0$, $V(0) = 0$, satisfies the Hamilton–Jacobi inequality (HJI)

$$e^{\top}Re + \nabla V^{\top}\big(\mathcal F + (C\otimes I_m)\mathcal G\big) + \frac{1}{4\rho^2}\nabla V^{\top}\mathcal H\mathcal H^{\top}\nabla V + \frac12\,\mathrm{tr}\big(\Sigma^{\top}\nabla^2V\,\Sigma\big) \ \le\ 0$$

along the error dynamics. Then the $H_\infty$ noise-filtering property holds with level $\rho$: intrinsic parameter fluctuations do not destroy synchronization, and the effect of extrinsic noise on the synchronization error is at most $\rho$ in the mean-energy sense. The best achievable level is $\rho_0 = \inf\{\rho : \text{the HJI has a solution } V \ge 0\}$, which can be lowered by tuning kinetic parameters or by adding an external control input.

Approximating the nonlinear error dynamics by a fuzzy interpolation of local linear systems turns the HJI, for quadratic $V(e) = e^{\top}Pe$, into a family of linear matrix inequalities in $P > 0$, giving a computable design criterion.

## Expansion

By Itô's formula, $dV(e) = \big[\nabla V^{\top}(\mathcal F + (C\otimes I)\mathcal G + \mathcal H v) + \frac12\mathrm{tr}(\Sigma^{\top}\nabla^2V\Sigma)\big]dt + \nabla V^{\top}\Sigma\,dw$. Completing the square,

$$\nabla V^{\top}\mathcal H v \le \frac{1}{4\rho^2}\nabla V^{\top}\mathcal H\mathcal H^{\top}\nabla V + \rho^2 v^{\top}v,$$

so the HJI gives a drift at most $-e^{\top}Re + \rho^2v^{\top}v$. Taking expectations (the stochastic integral has mean zero under the usual integrability conditions) and integrating over $[0, t_f]$ yields $\mathbb E V(e(t_f)) - \mathbb E V(e(0)) \le -\mathbb E\int e^{\top}Re + \rho^2\mathbb E\int v^{\top}v$, and $V \ge 0$ gives the bound.

## Sources

- B.-S. Chen, C.-Y. Hsu, "Robust synchronization control scheme of a population of nonlinear stochastic synthetic genetic oscillators under intrinsic and extrinsic molecular noise via quorum sensing", BMC Systems Biology (2012), Eqs. (8)–(18), Proposition 1 (HJI criterion) and Proposition 2 (fuzzy LMI criterion), <https://doi.org/10.1186/1752-0509-6-136>, PMCID PMC3554485.
