# Saddle-node harvesting threshold under a strong Allee effect

Consider a population with strong Allee threshold $S$ and carrying capacity $K$, $0<S<K$, harvested at per-capita rate $\lambda\ge0$:

$$\frac{dX}{dt}=rX\Big(\frac{X}{S}-1\Big)\Big(1-\frac{X}{K}\Big)-\lambda X,\qquad r>0 .$$

With $Y=X/K$ and $\beta=K/S>1$ this is $\dot Y=rY(\beta Y-1)(1-Y)-\lambda Y$.

**Statement.** Let

$$\lambda_c=\frac{r(\beta-1)^2}{4\beta}.$$

1. If $0\le\lambda<\lambda_c$, there are three equilibria $0<Y_2<Y_3$ with

$$Y_{2,3}=\frac{(\beta+1)\mp\sqrt{(\beta+1)^2-4\beta(1+\lambda/r)}}{2\beta};$$

$0$ and $Y_3$ are locally asymptotically stable and $Y_2$ (the harvested Allee threshold) is unstable; solutions with $Y(0)<Y_2$ go extinct and those with $Y(0)>Y_2$ converge to $Y_3$.
2. At $\lambda=\lambda_c$ the two positive equilibria merge at $Y_m=\frac{\beta+1}{2\beta}$ (saddle-node bifurcation).
3. If $\lambda>\lambda_c$, $0$ is the only equilibrium and every solution goes extinct.

As $\lambda$ increases to $\lambda_c$, $Y_3$ decreases and $Y_2$ increases, so the gap $Y_3-Y_2=\frac{1}{\beta}\sqrt{(\beta+1)^2-4\beta(1+\lambda/r)}$ closes; maximizing the yield $\lambda Y_3(\lambda)$ pushes the stock towards the extinction threshold, which under multiplicative noise $\epsilon Y\,dB_t$ shortens the expected time to extinction.

## Expansion

Positive equilibria solve $r(\beta Y-1)(1-Y)=\lambda$, i.e. $\beta Y^2-(\beta+1)Y+(1+\lambda/r)=0$, whose discriminant $(\beta+1)^2-4\beta(1+\lambda/r)$ is positive exactly when $\lambda<\lambda_c$; both roots are positive since their sum and product are positive. Stability follows from the sign of the cubic right-hand side, which is negative on $(0,Y_2)$, positive on $(Y_2,Y_3)$ and negative beyond $Y_3$; equivalently the dynamics are a gradient flow in a double-well potential. For $\lambda>\lambda_c$ the right-hand side is negative for all $Y>0$.

## Sources

- A. Tesfay, D. Tesfay, J. Brannan and J. Duan, *A Logistic-Harvest Model with Allee Effect under Multiplicative Noise*, arXiv:2008.01692 (2020), <https://doi.org/10.48550/arXiv.2008.01692>. Section 4.1 (Equations 4.1–4.2, equilibria and the critical harvesting rate) and Section 4.2 (stochastic model, Equation 4.3).
