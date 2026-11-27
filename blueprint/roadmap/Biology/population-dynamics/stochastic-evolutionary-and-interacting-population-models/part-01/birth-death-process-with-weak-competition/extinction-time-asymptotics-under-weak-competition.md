# Extinction-time asymptotics of a birth–death process with weak competition

Let $X_\theta$ be the birth–death process on $\{0,1,2,\dots\}$ with birth rate $i\lambda$ and death rate $i\mu + i(i-1)\theta$ in state $i$: each individual reproduces at rate $\lambda$, dies of natural causes at rate $\mu$, and each ordered pair of individuals produces a competitive death at rate $\theta > 0$. The quadratic death term makes extinction certain; let $\tau_\theta$ be the extinction time and $\tau_0$ that of the linear process ($\theta = 0$). Define

$$c_1 = \frac{\lambda}{(\lambda-\mu)^2}\sqrt{\frac{2\pi}{\mu}}, \qquad c_2 = \lambda - \mu - \mu\ln\frac{\lambda}{\mu} \qquad (\lambda > \mu).$$

**Theorem 4.1 (fixed initial size).** Let $X_\theta(0) = m$ be fixed and couple $X_\theta$ with the linear process. As $\theta \to 0$:

1. if $\lambda \le \mu$, then $\tau_\theta \to \tau_0$ almost surely;
2. if $\lambda > \mu$, then $\tau_\theta \to \tau_0$ almost surely on $\{\tau_0 < \infty\}$, while on the survival event $\{\tau_0 = \infty\}$, for every $x \ge 0$, $\mathbb P\big(\tau_\theta > x\,c_1\sqrt\theta\,e^{c_2/\theta} \,\big|\, \tau_0 = \infty\big) \to e^{-x}$.

**Theorem 4.2 (initial size of order $1/\theta$).** Let $X_\theta(0) = m_\theta$ with $\theta m_\theta \to a > 0$. As $\theta \to 0$:

1. (supercritical, $\lambda > \mu$) $\mathbb E(\tau_\theta) \sim c_1\sqrt\theta\,e^{c_2/\theta}$ and $\mathbb P\big(\tau_\theta > x\,c_1\sqrt\theta\,e^{c_2/\theta}\big) \to e^{-x}$ for every $x \ge 0$;
2. (subcritical, $\lambda < \mu$) with $\gamma$ the Euler constant,

$$\mathbb E(\tau_\theta) = \frac{\ln(a/\theta) + \ln\frac{\mu-\lambda}{\mu} + \ln\frac{\mu-\lambda}{\mu-\lambda+a} + \gamma}{\mu-\lambda} + o(1),$$

and $(\mu-\lambda)\tau_\theta - \ln(a/\theta) - \ln\frac{\mu-\lambda}{\mu} - \ln\frac{\mu-\lambda}{\mu-\lambda+a}$ converges in law to the standard Gumbel distribution, $\mathbb P(\cdot \le x) \to e^{-e^{-x}}$;
3. (critical, $\lambda = \mu$) $\mathbb E(\tau_\theta) \sim (\pi/2)^{3/2}/\sqrt{\theta\mu}$.

So a supercritical population near its carrying capacity $(\lambda-\mu)/\theta$ persists for an exponentially long, memoryless time, a subcritical one dies in logarithmic time with Gumbel fluctuations, and the critical case sits in between at order $\theta^{-1/2}$.

## Expansion

For a birth–death chain the mean absorption time is an explicit series in the products $\pi_j = \prod_{i=0}^{j-1}\frac{\mu + \theta i}{\lambda}$. A Laplace-type approximation gives $\pi_j = (1 + j\theta/\mu)^{-1/2}\,e^{-W(j\theta)/\theta}(1 + o(1))$ uniformly for $j \le T/\theta$, with $W(x) = x - x\ln\frac{\mu+x}{\lambda} - \mu\ln\frac{\mu+x}{\mu}$; the minimum of $W$ at the carrying capacity produces $c_2$. In the supercritical case the process makes many excursions from the quasi-equilibrium level, each of expected length $\sim \sqrt{2\pi\theta/\lambda}/(\lambda-\mu)$, and each ends in extinction with probability $\sim \frac{(\lambda-\mu)\sqrt\mu}{\lambda^{3/2}}e^{-c_2/\theta}$, so the number of excursions is geometric and the rescaled time is exponential. In the subcritical case the process first follows the logistic ODE down to small sizes and then behaves like a linear subcritical process, whose extinction time from a large population is Gumbel.

## Sources

- Serik Sagitov, Altynay Shaimerdenova, "Extinction times for a birth-death process with weak competition", arXiv (2012); Lithuanian Mathematical Journal 53 (2013). Section 2 (model), Theorems 4.1 and 4.2, Lemmas 4.3, 5.1 and 5.2. <https://doi.org/10.48550/arXiv.1209.5182>. Published version: Lithuanian Mathematical Journal 53(2) (2013), 220–234, <https://doi.org/10.1007/s10986-013-9204-x>; locators above refer to the arXiv version.
