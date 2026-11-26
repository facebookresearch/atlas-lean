# Identifiability of the order in Caputo SIR models

**Model.** The Caputo SIR model with order $0<\alpha\le1$,
$${}^CD^\alpha_tS=-\beta\frac{SI}{N},\qquad {}^CD^\alpha_tI=\beta\frac{SI}{N}-\gamma I,\qquad {}^CD^\alpha_tR=\gamma I,$$
with $S(0)=N-I_0$, $I(0)=I_0$, $R(0)=0$ and known $N$, is observed through incidence $x(t)=\beta S(t)I(t)/N$; write $\theta=(\alpha,\beta,\gamma,I_0)$. For daily data it is discretized by the Grünwald-Letnikov (GL) scheme with weights $w_0=1$, $w_j=(1-\frac{\alpha+1}j)w_{j-1}$. A parameter is structurally identifiable if distinct values give distinct noise-free observations, and practically non-identifiable if the resulting observation distributions cannot be reliably separated.

**Theorem (time-varying transmission: structural non-identifiability).** If the transmission rate $\beta_t$ may vary freely, then for every admissible $(\alpha,\gamma,I_0)$ with $0<\gamma\le\alpha\le1$ (and an admissibility condition on the data ensuring $S_t>0$) there is a unique positive sequence $\beta_t=N\bar n_{t+1}/(S_tI_t)$ for which the GL model reproduces the smoothed incidence exactly. Hence order, removal rate and initial count are not identifiable from incidence in hybrid models.

**Theorem (constant transmission, exact data: structural identifiability).** If $x_1\ne0$, the order is determined by noise-free incidence on any interval $[0,\varepsilon]$: $\alpha=\lim_{t\to0^+}\log|x(t)-x_0|/\log t$.

**Theorem (early growth: bounded information).** Linearizing at the disease-free state, $I(t)=I_0E_\alpha(\lambda t^\alpha)$ with $\lambda=\beta-\gamma$ and $E_\alpha$ the Mittag-Leffler function, so
$$x_{\mathrm{lin}}(t)=Ae^{rt}+\rho_\theta(t),\qquad r=(\beta-\gamma)^{1/\alpha},\quad A=\frac{\beta I_0}{\alpha},\quad -\frac{\beta I_0C_\alpha}{\lambda t^\alpha}\le\rho_\theta(t)\le0,$$
with $C_\alpha=\Gamma(\alpha)/(\pi\sin\alpha\pi)$. The dominant term depends only on $(r,A)$, and the set $M(r,A)$ of parameters sharing them is two-dimensional (one free $\beta$ for each $\alpha$). For $\theta,\theta'\in M(r,A)$ and independent Poisson counts with means $x_{\mathrm{lin}}$,
$$\mathrm{KL}\big(P^T_\theta\,\|\,P^T_{\theta'}\big)\le K(\theta,\theta')<\infty\quad\text{for all }T,$$
so the total-variation distance stays below $\sqrt{K/2}$ and every test has summed error probabilities at least $1-\sqrt{K/2}$ however long the linear phase is observed. Sandwich bounds $(1-\varepsilon)\beta I_0E_\alpha((\lambda-\beta\varepsilon)t^\alpha)\le x(t)\le\beta I_0E_\alpha(\lambda t^\alpha)$ while $S\ge(1-\varepsilon)N$ transfer the bound to the nonlinear model during low depletion, and as $N\to\infty$ with fixed horizon the nonlinear KL divergence is bounded by the linear one plus a vanishing term.

## Depends on

- [Kermack-McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

The Mittag-Leffler function satisfies $E_\alpha(z)=\alpha^{-1}e^{z^{1/\alpha}}-(\text{a positive integral term})$, and the integral term is at most $C_\alpha/z$; so beyond a transient, early fractional growth is exactly exponential with rate $r$ and amplitude $A$, the same signature as an integer-order model with matched $(r,A)$. Because Poisson KL is bounded by $\sum_t(\mu_t-\nu_t)^2/\nu_t$, and the mean difference decays like $t^{-\alpha}$ while $\nu_t$ grows exponentially, the series converges. Information about $\alpha$ comes only from the transient and, later, from depletion near the epidemic peak; in simulations wrong orders are rejected only once the peak is in the data, fits indistinguishable early predict peaks differing by about 75%, and discretization or time-varying transmission can produce fitted orders below one without any memory.

## Sources

- M. B. Hossain, M. S. Alam, "Fractional order or false memory: identifiability of Caputo SIR models from incidence data", arXiv:2611.25440 (2026), Section 2 (model, Grünwald-Letnikov scheme, Definition 2.3), Section 3 (Assumption 3.1, Proposition 3.2, Corollary 3.3), Section 4 (Proposition 4.1) and Section 5 (Lemma 5.1, Theorem 5.2, Lemma 5.4, Propositions 5.5-5.6, Corollary 5.7), <https://doi.org/10.48550/arXiv.2611.25440>.
