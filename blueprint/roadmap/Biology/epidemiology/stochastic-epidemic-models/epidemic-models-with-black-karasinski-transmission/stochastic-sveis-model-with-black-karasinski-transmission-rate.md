# Stochastic SVEIS model with Black-Karasinski transmission rate

In the deterministic SVEIS model, susceptible ($S$), vaccinated ($V$), exposed ($E$) and infectious ($I$) hosts are recruited at rate $\Pi$, die at rate $m$, are vaccinated at rate $\alpha$, lose vaccine protection at rate $\omega$, progress from $E$ to $I$ at rate $\sigma$, move into $V$ at rates $\xi$ (from $E$) and $\gamma$ (from $I$), and $I$ suffers additional removal at rate $\eta$. Infection has the saturated incidence $\beta SI/(1+kI)$. Its basic reproduction number is

$$\mathcal R_0=\frac{\sigma\beta\Pi(m+\omega)}{m(m+\alpha+\omega)(m+\gamma+\eta)(m+\sigma+\xi)}.$$

Environmental fluctuations are introduced by letting the transmission rate follow a Black-Karasinski process: $\ln\beta$ is an Ornstein-Uhlenbeck process,

$$d\ln\beta=\theta(\ln\bar\beta-\ln\beta)\,dt+\delta\,dB(t),$$

with long-run level $\bar\beta$, reversion speed $\theta>0$ and volatility $\delta>0$, which keeps $\beta$ positive. With $z=\ln\beta-\ln\bar\beta$ the model becomes

$$\begin{aligned}
dS&=\Bigl(\Pi-\alpha S-\frac{\bar\beta e^zSI}{1+kI}-mS+\omega V\Bigr)dt,\\
dV&=\bigl(\alpha S+\gamma I+\xi E-(m+\omega)V\bigr)dt,\\
dE&=\Bigl(\frac{\bar\beta e^zSI}{1+kI}-(m+\sigma+\xi)E\Bigr)dt,\\
dI&=\bigl(\sigma E-(m+\gamma+\eta)I\bigr)dt,\\
dz&=-\theta z\,dt+\delta\,dB(t).
\end{aligned}$$

**Well-posedness.** For every initial value in $\mathbb R_+^4\times\mathbb R$ the system has a unique global solution almost surely, and it remains in the invariant set

$$\Gamma=\Bigl\{(S,V,E,I,z)\in\mathbb R_+^4\times\mathbb R:\ S+V+E+I\le\frac\Pi m,\ S\le S^0\Bigr\},$$

where $S^0$ is the susceptible level at the disease-free equilibrium.

The stationary law of $z$ is $\mathcal N(0,\delta^2/(2\theta))$, so $\mathbb E[e^{z}]=e^{\delta^2/(4\theta)}$ under stationarity: noise in $\ln\beta$ raises the mean transmission rate above $\bar\beta$.

## Expansion

The total population satisfies $\frac d{dt}(S+V+E+I)\le\Pi-m(S+V+E+I)$, which bounds the epidemiological variables. Global existence follows from the nonnegative $C^2$ Lyapunov function $\sum_x(x-1-\ln x)$ over the compartments plus a term in $z$, whose generator is bounded above, so the solution cannot explode in finite time.

## Sources

- L. Khammich and D. Kiouach, "Asymptotic analysis of a stochastic SVEIS epidemic model using Black-Karasinski process", *Global and Stochastic Analysis* 13(02) (2026), 127–137, Section 1 (deterministic model, $\mathcal R_0$, and the Black-Karasinski formulation of the stochastic model), Theorem 1 and Remark 1 (Section 2), <https://doi.org/10.64837/gsa.13.2.8> (preprint arXiv:2511.02882).
