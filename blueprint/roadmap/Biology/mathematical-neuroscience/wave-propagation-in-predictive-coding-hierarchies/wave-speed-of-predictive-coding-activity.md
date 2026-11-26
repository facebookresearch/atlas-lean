# Wave speed of predictive-coding activity

**Setting.** For the [predictive-coding layer recurrence](amplification-factor-of-the-predictive-coding-layer-recurrence.md) with $0\le\beta<1$, $0<\alpha<1$, $0<\lambda<1$, $\alpha+\lambda\le1$, the amplification factor expands near $\theta=0$ as $\rho(\theta)=\exp(-ic_0\theta-\sigma_0\theta^2+O(|\theta|^3))$, and, when $\alpha+\lambda=1$, near $\theta=\pi$ as $\rho(\theta+\pi)=-\exp(-ic_\pi\theta-\sigma_\pi\theta^2+O(|\theta|^3))$, where
$$c_0=\frac{\beta+\alpha-\lambda}{1-\beta},\quad\sigma_0=\frac{\beta(1-\alpha-\lambda)+\alpha+\lambda-(\lambda-\alpha)^2}{2(1-\beta)^2},\quad c_\pi=\frac{-\beta+\alpha-\lambda}{1+\beta},\quad\sigma_\pi=\frac{1-(\alpha-\lambda)^2}{2(1+\beta)^2},$$
with $\sigma_0,\sigma_\pi>0$.

**Result.** The fundamental solution is, to leading order, a Gaussian wave travelling at speed $c_0$ layers per step:
$$G_j^n\approx\frac{1}{\sqrt{4\pi\sigma_0n}}\exp\Big(-\frac{(j-c_0n)^2}{4\sigma_0n}\Big)$$
up to a remainder with a Gaussian bound in $(j-c_0n)/\sqrt n$ (and, for $\beta>0$, an exponentially small tail far ahead). Activity propagates forward (up the hierarchy) iff $\alpha+\beta>\lambda$, backward iff $\alpha+\beta<\lambda$, and stalls when $\alpha+\beta=\lambda$. When $\alpha+\lambda=1$ a secondary wave at speed $c_\pi$ appears, with $c_\pi<0$ iff $\alpha<\beta+\lambda$, $0<c_\pi<c_0$ when $\beta+\lambda<\alpha$, and $c_\pi=0$ (blocked) when $\beta+\lambda=\alpha$; for $\beta=0$ the two waves coincide and the profile carries a factor $1+(-1)^{n+j}$.

For $\beta=0$ the scheme is explicit: solutions stay non-negative for non-negative data and $G_j^n=0$ for $|j|>n$, so $c_0=\alpha-\lambda\in(-1,1)$. For $\beta>0$ it is implicit, $G_j^n=0$ only for $j<-n$, and $c_0\to+\infty$ as $\beta\to1^-$.

## Expansion

The speed and diffusivity are the first two coefficients of $\log\rho$ at its tangency points with the unit circle; local limit theorems for such finite-difference schemes turn the expansion into the Gaussian approximation of $G^n$. The feedforward parameters $\alpha,\beta$ push activity up the hierarchy and the feedback parameter $\lambda$ pulls it down, and the sign of $c_0$ records which wins.

## Sources

- G. Faye, G. Fouilhé, R. VanRullen, "Mathematical derivation of wave propagation properties in hierarchical neural networks with predictive coding feedback dynamics", Bulletin of Mathematical Biology 85 (2023), Sections "Study of the Amplification Factor Function", "Turning Off the Instantaneous Feedforward Connections: Case β = 0" and "Turning On the Instantaneous Feedforward Connections: Case β > 0", Theorem 1 and Equation (11), <https://doi.org/10.1007/s11538-023-01186-9>, PMCID PMC10382470.
