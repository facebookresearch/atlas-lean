# Global positive solution of a white-noise transmission model

Environmental noise is introduced into a deterministic compartmental model by perturbing transmission rates, $\beta_1\mapsto\beta_1+\eta_1\dot B(t)$ and $\beta_2\mapsto\beta_2+\eta_2\dot B(t)$, where $B$ is a standard Brownian motion on a filtered probability space and $\eta_1,\eta_2>0$ are noise intensities. For an SIR model with an environmental reservoir $w$ (virus shed at rate $\alpha$ and removed at rate $\eta$) this gives the Itô system

$$
\begin{aligned}
ds&=\big(\Pi-(\beta_1 i+\beta_2 w)s-ds\big)\,dt-(\eta_1 si+\eta_2 sw)\,dB(t),\\
di&=\big((\beta_1 i+\beta_2 w)s-(d+d_1+\sigma)i\big)\,dt+(\eta_1 si+\eta_2 sw)\,dB(t),\\
dr&=(\sigma i-dr)\,dt,\qquad dw=(\alpha i-\eta w)\,dt,
\end{aligned}
$$

with recruitment $\Pi$, natural and disease death rates $d,d_1$, and recovery rate $\sigma$. With $\eta_1=\eta_2=0$ it reduces to the deterministic model, whose basic reproduction number is

$$
R_0=\frac{\Pi\beta_1}{d(d+d_1+\sigma)}+\frac{\alpha\Pi\beta_2}{d\,\eta\,(d+d_1+\sigma)} .
$$

**Theorem.** For every initial value $(s(0),i(0),r(0),w(0))\in\mathbb{R}^4_{+}$ there is a unique solution $(s,i,r,w)$ defined for all $t\ge 0$, and it remains in $\mathbb{R}^4_{+}$ almost surely. Moreover, along solutions $d(s+i+r)\le(\Pi-d(s+i+r))\,dt$ and $dw\le(\alpha i-\eta w)\,dt$, so

$$
\Omega=\Big\{(s,i,r,w)\in\mathbb{R}^4_{+}:\ s+i+r\le\frac{\Pi}{d},\ w\le\frac{\alpha\Pi}{\eta d}\Big\}
$$

is positively invariant.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The noise enters $ds$ and $di$ with opposite signs, so the total population $s+i+r$ obeys a noise-free inequality, which gives the bounds defining $\Omega$. The coefficients are locally Lipschitz, so a unique local solution exists up to an explosion time $\tau_e$. To show $\tau_e=\infty$, define stopping times $\tau_k$ at which some component first leaves $(1/k,k)$, and apply Itô's formula to a nonnegative function of logarithmic type, for example $V=\sum_x (x-1-\ln x)$ over the four compartments. On the bounded region the generator satisfies $\mathcal{L}V\le K$ for a constant $K$, so $\mathbb{E}\,V(x(\tau_k\wedge T))\le V(x(0))+KT$. If $\tau_\infty\le T$ with positive probability, $V$ at $\tau_k$ is at least $\min(k-1-\ln k,\ 1/k-1+\ln k)\to\infty$, a contradiction. Hence $\tau_\infty=\infty$ almost surely and solutions stay positive. Extinction and persistence-in-mean results then compare $\frac1t\ln i(t)$ with a noise-corrected threshold, by the strong law for the martingale terms $\frac1t\int_0^t s\,i\,dB$.

## Sources

- T. Khan, G. Zaman, Y. El-Khatib, "Modeling the dynamics of novel coronavirus (COVID-19) via stochastic epidemic model", *Results in Physics* 24 (2021) 104004. <https://doi.org/10.1016/j.rinp.2021.104004>. PMCID: PMC7999738. (Model (1), Eq. (6), Theorem 2, Remark 1, Eq. (30).)
