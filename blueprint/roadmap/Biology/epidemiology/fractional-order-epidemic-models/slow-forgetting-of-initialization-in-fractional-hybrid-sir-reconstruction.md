# Slow forgetting of initialization in fractional hybrid SIR reconstruction

**Model.** A hybrid SIR forecaster reconstructs a daily transmission rate from reported cases and then forecasts it. In the Caputo version of order $\alpha\in(0,1]$,

$${}^CD^\alpha_tS=-\beta(t)\frac{SI}N,\qquad {}^CD^\alpha_tI=\beta(t)\frac{SI}N-\gamma I,\qquad {}^CD^\alpha_tR=\gamma I .$$

For every $T>0$ there is a unique continuous solution with $S+I+R=N$ and $S,I,R\ge0$. With constant $\beta$, every $(S_*,0,N-S_*)$ is an equilibrium, and the linearized infectious component ${}^CD^\alpha y=\lambda y$, $\lambda=\beta S_*/N-\gamma$, has solution $y(0)E_\alpha(\lambda t^\alpha)$, which decays iff $\beta S_*/(\gamma N)<1$.

**Grünwald-Letnikov reconstruction.** With unit step, weights $w_0=1$, $w_j=(1-\frac{\alpha+1}j)w_{j-1}$ (so $w_1=-\alpha$, $w_j<0$, tails $\tau_n=\sum_{j>n}|w_j|=\frac{\Gamma(n+1-\alpha)}{\Gamma(1-\alpha)\Gamma(n+1)}\sim\frac{n^{-\alpha}}{\Gamma(1-\alpha)}$), and smoothed reported incidence $\bar n_t$ identified with $\beta_tS_tI_t/N$, the states follow explicit recursions such as

$$I_{t+1}=I_0+\bar n_{t+1}-\gamma I_t-\sum_{j=1}^{t+1}w_j(I_{t+1-j}-I_0),\qquad \beta_t=\frac{N\bar n_{t+1}}{S_tI_t}.$$

At $\alpha=1$ they reduce exactly to the integer-order reconstruction $S_{t+1}=S_t-\bar n_{t+1}$, $I_{t+1}=(1-\gamma)I_t+\bar n_{t+1}$. They conserve $S+I+R=N$, and if $0<\gamma\le\alpha\le1$, $I_t,R_t\ge0$, since $I_{t+1}=\bar n_{t+1}+(\alpha-\gamma)I_t+\sum_{j\ge2}|w_j|I_{t+1-j}+\tau_{t+1}I_0$.

**Theorem (slow forgetting of the initial infectious count).** Let $0<\gamma\le\alpha<1$ and perturb $I_0$ to $I_0+\delta$ with the incidence series fixed. The error $e_t=I^{(\delta)}_t-I_t$ keeps the sign of $\delta$, satisfies $|e_t|\le(1-\gamma)|\delta|$ and $e_t\to0$, but

$$|e_t|\ \ge\ |\delta|\,\tau_t=|\delta|\frac{\Gamma(t+1-\alpha)}{\Gamma(1-\alpha)\Gamma(t+1)}\ \sim\ \frac{|\delta|\,t^{-\alpha}}{\Gamma(1-\alpha)} .$$

For integer order the error decays geometrically like $(1-\gamma)^t$, so after 332 daily steps the initialization effect at $\alpha=0.9$ is about $4.4\times10^8$ times larger than at $\alpha=1$.

## Depends on

- [Identifiability of the order in Caputo SIR models](identifiability-of-the-order-in-caputo-sir-models.md)

## Expansion

Subtracting the two reconstructions gives the linear recursion $e_{t+1}=(\alpha-\gamma)e_t+\sum_{j=2}^{t+1}|w_j|e_{t+1-j}+\tau_{t+1}\delta$, $e_0=\delta$, with non-negative coefficients when $\gamma\le\alpha$, which gives the sign property. Keeping only the last term gives the lower bound; using $\sum_{j=2}^{t+1}|w_j|=1-\alpha-\tau_{t+1}$ gives the upper bound and convergence. The algebraic tail of the GL weights is the discrete signature of the power-law memory kernel of the Caputo derivative: every past state, including the uncertain initial condition, keeps a weight decaying like $t^{-\alpha}$. Out-of-sample forecasting on Bangladesh and United States COVID-19 data found the integer order best in most Bangladesh settings, and mixed, non-significant gains from fractional orders in the United States, consistent with memory damping over-responsive forecasts rather than with genuine epidemiological memory.

## Sources

- M. B. Hossain, M. S. Alam, "Fractional-order hybrid SIR forecasting of COVID-19 in Bangladesh and the United States: memory effects and out-of-sample evaluation", arXiv:2611.13590 (2026), Section 2 (Definition 2.1, Lemmas 2.2-2.3), Section 3 (Theorem 3.1, Proposition 3.2), Section 4 (Propositions 4.1-4.2) and Section 5 (Theorem 5.1), <https://doi.org/10.48550/arXiv.2611.13590>.
