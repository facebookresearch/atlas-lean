# Extinction and persistence thresholds of the stochastic food-chain chemostat with Lévy jumps

**Model.** Let $S(t)$, $x(t)$, $y(t)$ be the concentrations of nutrient, prey and predator in a chemostat with feed concentration $S^0>0$. Each rate parameter is given only as an interval $[f^l,f^u]$ with $f^l,f^u>0$ and is represented, for a fixed $p\in[0,1]$, by $f_p=(f^l)^{1-p}(f^u)^p$; this is applied to the dilution rate $D$, uptake rates $m_1,m_2$, yields $\delta_1,\delta_2$ and noise intensities $\sigma_1,\sigma_2,\sigma_3$. The dynamics are

$$dS=\Bigl[D_p(S^0-S)-\tfrac{m_{1,p}}{\delta_{1,p}}Sx\Bigr]dt+\sigma_{1,p}S\,dB_1+\int_{\mathbb Y}\gamma_1(u)S(t^-)\,\widetilde N(dt,du),$$

$$dx=\Bigl[m_{1,p}Sx-D_px-\tfrac{m_{2,p}}{\delta_{2,p}}xy\Bigr]dt+\sigma_{2,p}x\,dB_2+\int_{\mathbb Y}\gamma_2(u)x(t^-)\,\widetilde N(dt,du),$$

$$dy=\bigl[m_{2,p}xy-D_py\bigr]dt+\sigma_{3,p}y\,dB_3+\int_{\mathbb Y}\gamma_3(u)y(t^-)\,\widetilde N(dt,du),$$

where $B_1,B_2,B_3$ are independent Brownian motions, $\widetilde N$ is a compensated Poisson random measure independent of them with finite characteristic measure $\lambda$ on $\mathbb Y\subset(0,\infty)$, and the jump sizes satisfy $\gamma_i(u)>-1$, are bounded, and $\int_{\mathbb Y}[\ln(1+\gamma_i(u))]^2\lambda(du)<\infty$. Set

$$\beta_i=\tfrac12\sigma_{i,p}^2+\int_{\mathbb Y}\bigl[\gamma_i(u)-\ln(1+\gamma_i(u))\bigr]\lambda(du),$$

$$R_0^s=\frac{S^0m_{1,p}}{D_p+\beta_2},\qquad R_1^s=\frac{S^0m_{1,p}m_{2,p}\delta_{1,p}}{m_{2,p}\delta_{1,p}(D_p+\beta_2)+m_{1,p}(D_p+\beta_3)},$$

and $\langle f\rangle_t=t^{-1}\int_0^tf(s)\,ds$.

**Theorem.** For every positive initial value there is a unique global solution that stays in $\mathbb R^3_+$ almost surely (under local Lipschitz and boundedness conditions on the jump coefficients). Assume moreover the moment condition $D_p-\frac{\theta-1}{2}\sigma^2-\frac{\zeta}{\theta}>0$ for some $\theta>2$, where $\sigma^2=\max_i\sigma_{i,p}^2$ and $\zeta$ is the jump moment term of the source. Then, almost surely:

1. **Both species die out** if $R_0^s<1$: $\limsup_{t\to\infty}t^{-1}\ln x(t)\le(D_p+\beta_2)(R_0^s-1)<0$, $\limsup_{t\to\infty}t^{-1}\ln y(t)\le-(D_p+\beta_3)<0$, and $\langle S\rangle_t\to S^0$.
2. **Predator dies out, prey persists** if $R_1^s<1<R_0^s$: $\limsup_{t\to\infty}t^{-1}\ln y(t)\le\bigl[\tfrac{m_{2,p}\delta_{1,p}}{m_{1,p}}(D_p+\beta_2)+D_p+\beta_3\bigr]\,(R_1^s-1)<0$, while

$$\langle S\rangle_t\to\frac{D_p+\beta_2}{m_{1,p}},\qquad \langle x\rangle_t\to\frac{\delta_{1,p}}{m_{1,p}}(D_p+\beta_2)(R_0^s-1).$$

3. **Predator persists in the mean** if $R_1^s>1$:

$$\liminf_{t\to\infty}\langle y\rangle_t\ge\frac{m_{1,p}\delta_{2,p}}{m_{1,p}m_{2,p}+m_{2,p}^2\delta_{1,p}}\Bigl[\tfrac{m_{2,p}\delta_{1,p}}{m_{1,p}}(D_p+\beta_2)+D_p+\beta_3\Bigr]\,(R_1^s-1)>0.$$

Since $R_1^s<R_0^s$, the two thresholds split the parameter space into total washout, prey-only and three-level coexistence regimes. White noise and jumps enter only through the effective death rates $D_p+\beta_i$, so they can drive species extinct even when the corresponding deterministic chemostat sustains them.

## Depends on

- [Chemostat equilibria and the washout threshold](../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

Positivity and non-explosion follow from a Lyapunov function of the form $\sum(z-c-c\ln(z/c))$ with stopping times. The moment condition gives $S(t)/t$, $x(t)/t$, $y(t)/t\to0$ and the martingale terms divided by $t$ vanish (strong law for local martingales). Integrating a linear combination of the three equations shows that $\langle S\rangle_t+\frac{1}{\delta_1}\langle x\rangle_t+\frac{1}{\delta_1\delta_2}\langle y\rangle_t$ (with parameters at level $p$) tends to $S^0$ up to $o(1)$ terms. Applying Itô's formula to $\ln x$ and $\ln y$ gives $t^{-1}\ln x=m_{1,p}\langle S\rangle_t-(D_p+\beta_2)-\frac{m_{2,p}}{\delta_{2,p}}\langle y\rangle_t+o(1)$ and $t^{-1}\ln y=m_{2,p}\langle x\rangle_t-(D_p+\beta_3)+o(1)$; eliminating the averages with the conservation relation produces the bounds with factors $R_0^s-1$ and $R_1^s-1$.

## Sources

- F. Sun, *Dynamics of an imprecise stochastic Lotka–Volterra food chain chemostat model with Lévy jumps*, arXiv:2004.04307 (2020), Section 2 (model and thresholds), Theorem 3.1, Theorems 4.1 and 4.2, Theorem 5.1. The source writes the prey diffusion term as $\sigma_2S\,dB_2$ in its displayed system, but $\beta_2$ and the proofs correspond to the multiplicative form $\sigma_2x\,dB_2$ used here. <https://doi.org/10.48550/arXiv.2004.04307>
