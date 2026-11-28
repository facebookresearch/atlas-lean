# Weighted-stage peak of the SI(k)R model

**Model.** With transmission rate $\beta$, stage exit rate $\delta$ and $k\ge1$ infectious stages,

$$\dot S=-\beta SI,\qquad \dot I_1=\beta SI-\delta I_1,\qquad \dot I_i=\delta I_{i-1}-\delta I_i\ (2\le i\le k),\qquad \dot R=\delta I_k,$$

where $I=\sum_iI_i$, $S(0)=1-\varepsilon$, $I_1(0)=\varepsilon$, other stages empty. The infectious period is Erlang with mean $k/\delta$, so $R_0=\beta k/\delta$. Define the weighted stage functional (remaining infectious-stage mass)

$$V^{(k)}(t)=\sum_{i=1}^k(k-i+1)\,I_i(t)\le k\,I(t),\qquad W^{(k)}_{\max}=\max_t V^{(k)}(t)/k,\qquad I^{(k)}_{\max}=\max_tI(t).$$

**Proposition (explicit weighted peak).** If $1-\varepsilon>\delta/(k\beta)$,

$$V^{(k)}_{\max}=k-\frac\delta\beta-\frac\delta\beta\ln\frac{\beta k(1-\varepsilon)}{\delta},\qquad\text{i.e.}\qquad W^{(k)}_{\max}=1-\frac{1+\ln(R_0(1-\varepsilon))}{R_0},$$

the classical SIR peak formula, attained when $S=1/R_0$.

**Theorem (surrogate accuracy).** With $\beta,\delta$ fixed,

$$\frac{W^{(k)}_{\max}}{I^{(k)}_{\max}}=1-\frac\delta\beta\,\frac{\ln k}{k}+O(1/k),\qquad k\to\infty .$$

So $W_{\max}\le I_{\max}$ always, and in this regime (mean infectious period $k/\delta\to\infty$) the weighted peak matches the prevalence peak up to a relative error of order $\ln k/k$.

**Infinite-stage limit.** If the incidence $A^{(k)}=-\dot S^{(k)}$ converges locally uniformly to a continuous $A$, then with $\tau$ the limiting fixed infectious duration and $i_k=\lfloor kx\rfloor$, $kI^{(k)}_{i_k}(t)\to\tau A(t-\tau x)$ for $t>\tau x$: the stage profile becomes a transport of incidence along infection age. With a fixed infectious duration and an incidence peak broad relative to it, this gives the approximation $I_{\max}\approx2W_{\max}$. As the initial infected fraction $\varepsilon\to0$, a relative error $E=2W_{\max}/I_{\max}-1<\eta$ requires $R_0<R_0^\#(\eta)$, the root in $(1,\infty)$ of $(1+\ln R_0)/R_0=(1-\eta)/2$.

## Expansion

Differentiating, $\dot V=k\beta SI-\delta\sum_iI_i=k\beta SI-\delta I$, so $dV/dS=-k+\delta/(\beta S)$ and $V=k(1-\varepsilon-S)+\frac\delta\beta\ln\frac S{1-\varepsilon}+k\varepsilon$ along the trajectory. $V$ is maximal when $S=\delta/(k\beta)=1/R_0$, giving the formula. Since $V\le kI$, $W_{\max}\le I_{\max}$. When the infectious duration is fixed and the stage occupancies are close to a transported incidence profile, $V/k$ weights infection ages linearly from $1$ down to $0$, so it carries about half of the prevalence; hence the factor $2$ in the surrogate.

## Sources

- D. Tverskoi, A. Gothard, G. A. Rempala, "Approximating Peak Prevalence in Multistage SIR Epidemics", *Bulletin of Mathematical Biology* 88(11) (2026), 215, model (SIkR) and Eq. for $V^{(k)}$, Proposition 1, Theorems 1 and 2, Proposition 2, <https://doi.org/10.1007/s11538-026-01785-2> (preprint arXiv:2607.01014).
