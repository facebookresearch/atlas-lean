# Inmate population model with sentence-length structure and SIS prevalence

**Model.** Prisoners enter at rate $\lambda_t$ with initial sentence lengths drawn from a probability measure $q_t$ on $\mathbb{R}_+$ and leave either when their remaining sentence $r$ reaches $0$ or by death/removal at rate $d_t$. The density $\rho^r_t$ of prisoners by remaining sentence satisfies the McKendrick transport equation

$$\frac{\partial\rho^r_t}{\partial t} + d_t\rho^r_t = \frac{\partial\rho^r_t}{\partial r} + \lambda_t q'_t(r),$$

and the population $N_t = \int_0^\infty \rho^r_t\,dr$ obeys $\dot N_t = \lambda_t - \rho^0_t - d_tN_t$, with $\rho^0_t$ the release rate. Write $T_q$ for the mean of $q$, $\hat q(d) = \int e^{-d\alpha}q(d\alpha)$ for its Laplace transform, and $\mu^{\mathrm{in}} = \lambda/N$, $\mu^{\mathrm{out}} = \rho^0/N$ for the relative entry and exit rates.

**Theorem (time-independent parameters).**
1. *(Equilibrium density.)* Every finite-mass solution converges, and the limiting (unique finite-mass stationary) density is

$$\rho^r = \lambda\int_{(r,\infty)} e^{-d(\alpha - r)}\,q(d\alpha) \quad \text{for a.e. } r \ge 0.$$

2. *(Equilibrium size and turnover.)* $\mu^{\mathrm{out}} = \mu^{\mathrm{in}} - d$, and for $d > 0$

$$N = \lambda\,\frac{1 - \hat q(d)}{d}, \qquad \mu^{\mathrm{in}} = \frac{d}{1 - \hat q(d)}, \qquad \mu^{\mathrm{out}} = \mu^{\mathrm{in}}\,\hat q(d);$$

these are right-continuous at $d = 0$, where $N = \lambda T_q$ and $\mu^{\mathrm{in}} = \mu^{\mathrm{out}} = 1/T_q$.
3. *(Remaining sentence.)* For $d > 0$ the mean remaining sentence of the current inmates is $R_\rho = \frac{T_q}{1 - \hat q(d)} - \frac1d$.
4. *(Two sentence classes.)* With short and long sentence classes entering in proportions $p^1, p^2$ and common removal rate $d > 0$, $1/\mu^{\mathrm{in}} = p^1/\mu^{\mathrm{in},1} + p^2/\mu^{\mathrm{in},2}$; the equilibrium share $\pi^1$ of short-sentence inmates satisfies $\pi^1 \le p^1$, and $\mu^{\mathrm{in},2} \le \mu^{\mathrm{in}} \le \mu^{\mathrm{in},1}$.
5. *(SIS prevalence.)* For an SIS infection inside the prison with contact rate $\beta$, recovery rate $\gamma$ and a fraction $\alpha_I > 0$ of entrants already infected, the prevalence $x = I/N$ satisfies $\dot x = \alpha_I\mu^{\mathrm{in}} + \beta x(1 - x) - \gamma x - \mu^{\mathrm{in}}x$. The equilibrium prevalence $x_{\mathrm{eq}}$ of the one-class model and $\omega_{\mathrm{eq}}$ of the two-class (short/long sentence) model are both positive, and $x_{\mathrm{eq}} < \omega_{\mathrm{eq}}$ (resp. $>$, $=$) iff $\alpha_I < 1 - \gamma/\beta$ (resp. $>$, $=$).

## Expansion

Remaining sentence time plays the role of a reversed age: it decreases at unit speed, and inmates exit at $r = 0$, so the stationary density integrates the entry flow of sentences longer than $r$, discounted by survival $e^{-d(\alpha - r)}$. Laplace transforms of the sentence distribution give the equilibrium population and turnover in closed form, so these quantities can be estimated from histograms of imposed sentences. Turnover feeds infection dynamics because releases remove infected inmates and admissions import infection at rate $\alpha_I\mu^{\mathrm{in}}$: ignoring sentence heterogeneity misestimates prevalence, upward or downward according to whether imported prevalence exceeds the internal endemic level $1 - \gamma/\beta$.

## Sources

- P. Gajardo, V. Riquelme, "Inmate population models with nonhomogeneous sentence lengths and their effects in an epidemiological model", arXiv:2101.02097 (2021), Propositions 1–6, Lemmas 1–2, Corollary 1 and Proposition 7 (Section 3), <https://doi.org/10.48550/arXiv.2101.02097>.
