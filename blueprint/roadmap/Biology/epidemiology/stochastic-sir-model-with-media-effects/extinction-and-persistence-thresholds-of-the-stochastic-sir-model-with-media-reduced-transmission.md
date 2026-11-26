# Extinction and persistence thresholds of the stochastic SIR model with media-reduced transmission

Media coverage lowers the contact rate as prevalence grows, modelled by the factor $e^{-\alpha I}$ with $\alpha\ge0$. Environmental noise perturbs the transmission coefficient:

$$
\begin{aligned}
dS&=(\Lambda-\beta e^{-\alpha I}SI-\mu S)\,dt-\sigma e^{-\alpha I}SI\,dB,\\
dI&=\big(\beta e^{-\alpha I}SI-(\mu+\gamma)I\big)\,dt+\sigma e^{-\alpha I}SI\,dB,\\
dR&=(\gamma I-\mu R)\,dt,
\end{aligned}
$$

with $\Lambda,\beta,\mu,\gamma,\sigma>0$. For every positive initial value there is a unique global positive solution, and $\Gamma=\{S+I+R\le\Lambda/\mu\}$ is invariant. Define

$$
R_0^S=\frac{\beta\Lambda}{\mu(\mu+\gamma)}-\frac{\sigma^2\Lambda^2}{2\mu^2(\mu+\gamma)}.
$$

1. If $R_0^S<1$ and $\sigma^2<\mu\beta/\Lambda$, then a.s. $\limsup_{t\to\infty}t^{-1}\ln I(t)\le(\mu+\gamma)(R_0^S-1)<0$, and $R(t)\to0$ and $S(t)\to\Lambda/\mu$ exponentially.
2. If $\sigma^2>\beta^2/(2(\mu+\gamma))$ (large noise), then a.s. $\limsup_{t\to\infty}t^{-1}\ln I(t)\le\beta^2/(2\sigma^2)-\mu-\gamma<0$.
3. If $R_0^S>1$, the disease persists weakly: a.s. $\limsup_{t\to\infty}I(t)\ge\xi/(1+\gamma/\mu)$, where $\xi$ is the unique root in $(0,\Lambda/\mu)$ of

$$
\beta e^{-\alpha\xi}\big(\tfrac\Lambda\mu-\xi\big)-(\mu+\gamma)-\tfrac12\sigma^2e^{-2\alpha\xi}\big(\tfrac\Lambda\mu-\xi\big)^2=0.
$$

The threshold $R_0^S$ does not depend on the media parameter $\alpha$, as in the deterministic model. Noise lowers the threshold below the deterministic $R_0^D=\beta\Lambda/(\mu(\mu+\gamma))$, and large noise alone causes extinction.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

Apply Itô's formula to $\ln I$: $d\ln I=\big(\beta e^{-\alpha I}S-(\mu+\gamma)-\tfrac12\sigma^2e^{-2\alpha I}S^2\big)\,dt+\sigma e^{-\alpha I}S\,dB$. The drift is a concave quadratic in $u=e^{-\alpha I}S\in[0,\Lambda/\mu]$. When $\sigma^2<\mu\beta/\Lambda$ its maximum on that interval is at $u=\Lambda/\mu$, which gives $(\mu+\gamma)(R_0^S-1)$. Otherwise the unconstrained maximum $\beta^2/(2\sigma^2)$ bounds it. The media factor equals $1$ at $I=0$, so it does not enter the linearized threshold.

## Sources

- J. Li and Y. Xiao, "Analysis of a stochastic SIR model with media effects", arXiv:2309.08126 (2023), system (main), Theorem 2.1, Corollary 2.2, Theorems 2.3–2.5. <https://doi.org/10.48550/arXiv.2309.08126>
