# Gamma stationary law of the harvested stochastic logistic model

Let a population with intrinsic growth rate $r>0$ and carrying capacity $K>0$ be harvested at per-capita rate $\lambda\in[0,r)$ under multiplicative environmental noise of intensity $\epsilon>0$:

$$dX_t=\Big[rX_t\Big(1-\frac{X_t}{K}\Big)-\lambda X_t\Big]dt+\epsilon X_t\,dB_t,\qquad X_0=x_0>0 .$$

Write $r_1=r-\lambda$ and $K_1=K(1-\lambda/r)$, so the drift is $r_1X(1-X/K_1)$. In the variables $Y=X/K_1$, $\tau=r_1t$ the equation becomes

$$dY=Y(1-Y)\,d\tau+\gamma Y\,dB_\tau,\qquad \gamma=\frac{\epsilon}{\sqrt{r-\lambda}} .$$

**Statement.**
1. *Explicit strong solution.* For $y_0>0$ the solution is unique, global and a.s. positive:

$$Y_\tau=\frac{y_0\exp\big((1-\tfrac{\gamma^2}{2})\tau+\gamma B_\tau\big)}{1+y_0\int_0^\tau\exp\big((1-\tfrac{\gamma^2}{2})s+\gamma B_s\big)\,ds}.$$

2. *Stationary law.* If $\gamma^2<2$, equivalently $\epsilon^2<2(r-\lambda)$, the Fokker–Planck equation has the unique stationary density on $(0,\infty)$

$$p(y)=M\,y^{\frac{2}{\gamma^2}-2}e^{-2y/\gamma^2},$$

a Gamma law with shape $\frac{2}{\gamma^2}-1$ and scale $\frac{\gamma^2}{2}$, with mode $\max(1-\gamma^2,0)$. If $\gamma^2\ge2$ there is no stationary density, and for $\gamma^2>2$ the population goes extinct, $Y_\tau\to0$ a.s.
3. *Noise-induced transition.* As $y\to0$, $p(y)\to0$ for $\gamma^2<1$, $p$ stays bounded for $\gamma^2=1$, and $p(y)\to\infty$ for $1<\gamma^2<2$: the mode jumps from the deterministic equilibrium region to $0$ at $\gamma^2=1$ although the population still persists.

For $\epsilon=0$ the solution reduces to the deterministic harvested logistic curve, with sustainable yield $\lambda K(1-\lambda/r)$ maximized at $\lambda=r/2$. Noise lowers the effective harvest threshold from $\lambda<r$ to $\lambda<r-\epsilon^2/2$.

## Expansion

Harvesting at constant effort only rescales the logistic parameters, so everything reduces to the classical stochastic logistic equation. The substitution $Z=1/Y$ linearizes it, $dZ=[(\gamma^2-1)Z+1]\,d\tau-\gamma Z\,dB_\tau$, which is solved by variation of constants. The stationary density solves $\frac{d}{dy}(y(1-y)p)=\frac{\gamma^2}{2}\frac{d^2}{dy^2}(y^2p)$ with zero flux, giving $p\propto y^{-2}\exp(\int\frac{2(1-y)}{\gamma^2y}dy)$, integrable at $0$ exactly when $\frac{2}{\gamma^2}-2>-1$. Extinction for $\gamma^2>2$ is visible in the numerator of the explicit solution, whose exponential growth rate $1-\gamma^2/2$ is then negative.

## Sources

- A. Tesfay, D. Tesfay, J. Brannan and J. Duan, *A Logistic-Harvest Model with Allee Effect under Multiplicative Noise*, arXiv:2008.01692 (2020), <https://doi.org/10.48550/arXiv.2008.01692>. Section 3.2 (Equations 3.4–3.8, explicit solution); Section 3.3 (Theorem 1, Fokker–Planck equation, and the stationary density).
