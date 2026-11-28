# Critical delay in a delayed Beverton–Holt recurrence

**Model.** Let $z_t\ge0$ be the number of fecund individuals in generation $t$. Newborns need $\tau\in\mathbb Z_{\ge 1}$ steps to reach fecundity, and those that die during this delay do not contribute to growth. With parameters $a,b,c>0$, the model modifies the Beverton–Holt map as

$$z_{t+1}=\frac{1}{m(z_t)}\Big\{z_t+\frac{ab\,z_{t-\tau+1}}{M(z_{t-\tau+1})}\Big\}=:H(z_t,z_{t-\tau+1}),$$

where

$$m(x)=1+b+cx,\qquad M(x)=b\beta+(\beta-1)cx,\qquad\beta=(1+b)^\tau,$$

and the initial data $(z_0,\dots,z_{\tau-1})$ are nonnegative. (Remark: the undelayed case $\tau=0$ is excluded from the theorem below because $z_{t-\tau+1}=z_{t+1}$ makes the recurrence implicit, and $\beta=1$ makes the denominator $2c(\beta-1)$ vanish.) The **critical delay** is

$$\tau_c=\frac{\log(a/b)}{\log(1+b)}.$$

**Theorem.**

*(1)* (Equilibria) If $\tau\ge\lceil\tau_c\rceil$, the only nonnegative equilibrium is $0$. If $\tau<\lceil\tau_c\rceil$, there is also a unique positive equilibrium

$$\tilde z_+=\frac{-b(2\beta-1)+\sqrt{b^2(2\beta-1)^2+4b(a-b\beta)(\beta-1)}}{2c(\beta-1)}.$$

*(2)* (Extinction) If $\tau\ge\lceil\tau_c\rceil$, the zero equilibrium is globally asymptotically stable for all nonnegative initial conditions.

*(3)* (Persistence) If $\tau<\lceil\tau_c\rceil$, then $0$ is unstable and $\tilde z_+$ is globally asymptotically stable for all initial conditions $\vec z_0\not\equiv0$.

*(4)* The positive equilibrium decreases as the delay $\tau$ increases.

## Expansion

The quantity $a/(1+b)^\tau$ plays the role of the expected number of new fecund individuals produced per individual: $a$ newborns per step, each of which survives the $\tau$-step delay with probability $(1+b)^{-\tau}$ in the linearization. Extinction occurs exactly when this falls to $b$ or below, i.e. $\tau\ge\tau_c$, so maturation delay alone can drive a population extinct. This contrasts with the delayed logistic difference equation (a discretization of Hutchinson's equation), where delay causes oscillations rather than a sharp extinction threshold. Local stability follows from the companion structure of powers of the Jacobian. Global stability is proved in two regimes. When $c\tilde z_+\le1$ (equivalently $a\le\frac{1+b}{b}(b\beta+\beta-1)$), $H$ is increasing in both arguments and a contraction-type argument applies. When $c\tilde z_+>1$, orbits eventually enter $[\chi,U]$ with $\chi=\frac{b(1+b)\beta}{c(ab-(\beta-1)(1+b))}$, where $H$ is decreasing in its first argument and maps the box into itself, and an embedding into a monotone system gives convergence.

## Sources

- Sabrina H. Streipert, Gail S. K. Wolkowicz, "An alternative delayed population growth difference equation model", arXiv:2010.04378 (2020), Section 2 (model, eqs. for $H$, $m$, $M$, $\tau_c$), Theorems 3.2, 3.6, 3.7, 3.11 and 3.14, Propositions 3.8, 3.12–3.13, <https://doi.org/10.48550/arXiv.2010.04378>.
