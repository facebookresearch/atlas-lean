# Stationary distribution and extinction of the Black-Karasinski SVEIS model

Consider the [stochastic SVEIS model with Black-Karasinski transmission rate](stochastic-sveis-model-with-black-karasinski-transmission-rate.md), with long-run transmission level $\bar\beta$, reversion speed $\theta$, volatility $\delta$, deterministic reproduction number $\mathcal R_0$ and disease-free susceptible level $S^0$.

**Persistence in distribution.** Let

$$\mathcal R_0^s=\frac{\bar\beta\Pi\sigma(m+\omega)\,e^{\delta^2/(16\theta)}}{m(m+\alpha+\omega)(m+\gamma+\eta)(m+\sigma+\xi)}.$$

If $\mathcal R_0^s>1$, the stochastic system has at least one ergodic stationary distribution on $\Gamma$.

**Extinction.** For every initial value in $\Gamma$, almost surely

$$\limsup_{t\to\infty}\frac1t\ln\Bigl(\frac{\omega_1}{m+\sigma+\xi}E(t)+\frac{\omega_2}{m+\gamma+\eta}I(t)\Bigr)\le\min\{m+\sigma+\xi,\ m+\gamma+\eta\}\,(\mathcal R_0^e-1),$$

where $\omega_1=\sigma/\bigl((m+\gamma+\eta)\sqrt{\mathcal R_0}\bigr)$, $\omega_2=1$, and

$$\mathcal R_0^e=\sqrt{\mathcal R_0}+\frac{\sigma S^0\bar\beta\sqrt{e^{\delta^2/\theta}-2e^{\delta^2/(4\theta)}+1}}{\sqrt{\mathcal R_0}\,(m+\sigma+\xi)\min(m+\sigma+\xi,\ m+\gamma+\eta)}.$$

In particular, if $\mathcal R_0^e<1$, then $E(t)\to0$ and $I(t)\to0$ almost surely.

As $\delta\to0$ the noise corrections vanish: $\mathcal R_0^s$ tends to $\mathcal R_0$ evaluated at $\beta=\bar\beta$ and $\mathcal R_0^e$ tends to $\sqrt{\mathcal R_0}$, so both conditions reduce to comparing $\mathcal R_0$ with $1$.

## Depends on

- [Stochastic SVEIS model with Black-Karasinski transmission rate](stochastic-sveis-model-with-black-karasinski-transmission-rate.md)

## Expansion

The stationary distribution is obtained from a Khasminskii-type criterion: a Lyapunov function combining logarithmic terms in the compartments and a term in $z$ has generator bounded above by a negative constant outside a compact subset of the interior of $\Gamma$ when $\mathcal R_0^s>1$. Extinction uses the weights $(\omega_1,\omega_2)$ of the linearized infected subsystem: Itô's formula for the logarithm of the weighted sum, the bound $S\le S^0$, and the ergodic theorem for the Ornstein-Uhlenbeck process $z$ control the random excess $\bar\beta(e^z-1)$ by its stationary $L^2$ norm, $\sqrt{\mathbb E[(e^z-1)^2]}=\sqrt{e^{\delta^2/\theta}-2e^{\delta^2/(4\theta)}+1}$.

## Sources

- L. Khammich and D. Kiouach, "Asymptotic analysis of a stochastic SVEIS epidemic model using Black-Karasinski process", *Global and Stochastic Analysis* 13(02) (2026), 127–137, Theorem 2 (Section 3) and Theorem 3 (Section 4), <https://doi.org/10.64837/gsa.13.2.8> (preprint arXiv:2511.02882).
