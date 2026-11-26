# Moustakides' theorem: optimality of CUSUM under Lorden's criterion

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Assume $P_0 \ne P_1$, let $c > 0$, and let $\gamma = \mathsf{E}_\infty[N_c] \in [0, \infty]$ be the mean time to false alarm of the [CUSUM alarm](cusum-time.md) $N_c = \inf\{n \ge 1 : W_n \ge c\}$, where $\mathsf{E}_\infty$ is the expectation under $P_0^{\otimes \mathbb{N}}$ (no change). Then for every stopping time $T$ of the [observation filtration](observation-filtration.md) with $\mathsf{E}_\infty[T] \ge \gamma$,

$$\overline{\mathrm{WADD}}(N_c) \le \overline{\mathrm{WADD}}(T),$$

where $\overline{\mathrm{WADD}}(T) = \sup_\nu \operatorname{ess\,sup} \mathsf{E}_\nu[(T - \nu + 1)^+ \mid X_1, \dots, X_{\nu-1}]$ is [Lorden's worst-case delay](lorden-delay.md) (Moustakides 1986, as stated in Lai 2001, §3, p. 316; Lorden 1971 had proved asymptotic optimality as $\gamma \to \infty$). Lai writes CUSUM with the statistic $\max_{1 \le k \le n} \sum_{i=k}^{n} \log L(X_i)$; for $c > 0$ it crosses $c$ at the same time as Page's statistic $W_n$ of the statement above (Veeravalli–Banerjee, remark after equation (48)).

## Sources

- T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica 11 (2001) 303–408, §3, p. 316, statement of Moustakides' theorem (G. V. Moustakides, *Optimal stopping times for detecting changes in distributions*, Ann. Statist. 14 (1986) 1379–1387; original not consulted, statement as given in Lai 2001) and of Lorden's asymptotic result (G. Lorden, *Procedures for reacting to a change in distribution*, Ann. Math. Statist. 42 (1971) 1897–1908; original not consulted).
- Venugopal V. Veeravalli and Taposh Banerjee, *Quickest change detection*, arXiv:1210.5552v1, 2012, §IV, after (53), and §IV-B, Corollary 3.

## Background

- [Closed form of the CUSUM statistic](page-cusum-eq-sup.md): the maximum-likelihood form of CUSUM.
- [Wald–Wolfowitz theorem: optimality of the SPRT](sprt-wald-wolfowitz.md): Lorden's asymptotic lower bound uses the exact optimality of the SPRT (Veeravalli–Banerjee, §IV-B).
