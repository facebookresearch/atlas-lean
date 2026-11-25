# Gluing two weak solutions over a common initial value and Brownian motion

Throughout, $W=C([0,\infty),\mathbb R)$ with its Borel $\sigma$-algebra (a Polish space), $b,\sigma:\mathbb R\to\mathbb R$ are Borel, and the stochastic differential equation is

$$dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t .$$

A weak solution is a filtered probability space $(\Omega,\mathcal A,P,(\mathcal F_t))$ with an $(\mathcal F_t)$-Brownian motion $B$ (adapted, with $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$) and a continuous adapted process $X$ with $\int_0^t(|b(X_s)|+\sigma(X_s)^2)\,ds<\infty$ almost surely and $X_t=X_0+\int_0^tb(X_s)\,ds+\int_0^t\sigma(X_s)\,dB_s$ for all $t$. Pathwise uniqueness holds if any two weak solutions on the same filtered space, with the same Brownian motion and $X_0=X'_0$ almost surely, are indistinguishable.

**Theorem.** Let $(X^i,B^i)$ on $(\Omega_i,\mathcal A_i,P_i,(\mathcal F^i_t))$, $i=1,2$, be weak solutions such that $(X^1_0,B^1)$ and $(X^2_0,B^2)$ have the same law $\nu$ on $\mathbb R\times W$. Let $Q_i(x_0,w;dy)$ be a [regular conditional distribution](../../foundations/regular-conditional-distributions/regular-conditional-distribution.md) of $X^i$ given $(X^i_0,B^i)$, and on $\hat\Omega=W\times W\times\mathbb R\times W$ with coordinates $(y_1,y_2,x_0,w)$ define

$$\hat P(dy_1,dy_2,dx_0,dw)=Q_1(x_0,w;dy_1)\,Q_2(x_0,w;dy_2)\,\nu(dx_0,dw).$$

Let $(\hat{\mathcal F}_t)$ be the usual augmentation under $\hat P$ of $\sigma(y_1|_{[0,t]},y_2|_{[0,t]},x_0,w|_{[0,t]})$. Then under $\hat P$, $w$ is an $(\hat{\mathcal F}_t)$-Brownian motion, $y_1(0)=y_2(0)=x_0$ almost surely, the law of $(y_i,w)$ equals the law of $(X^i,B^i)$, and both $(y_1,w)$ and $(y_2,w)$ are weak solutions on $(\hat\Omega,\hat P,(\hat{\mathcal F}_t))$ driven by the same Brownian motion $w$.

## Depends on

- [Regular conditional distribution (measure-valued family)](../../foundations/regular-conditional-distributions/regular-conditional-distribution.md)

## Proof depends on

- [Continuous modification of the Itô integral](../it-integral/ito-integral-continuous-modification.md)
- [Martingales and martingale problems are preserved by the usual augmentation](../../martingales/stopping-times-and-martingale-problems/martingales-and-martingale-problems-are-preserve.md)

## Expansion

A full proof shows that for $A\in\sigma(y|_{[0,t]})$ the map $(x_0,w)\mapsto Q_i(x_0,w;A)$ is measurable for the $\nu$-completion of $\sigma(x_0,w|_{[0,t]})$, because the future increments $(B^i_{t+s}-B^i_t)_{s\ge0}$ are independent of $(X^i_0,X^i|_{[0,t]},B^i|_{[0,t]})$. From this it checks that the canonical coordinate $w$ has increments after $t$ independent of $\hat{\mathcal F}_t$, so it is an $(\hat{\mathcal F}_t)$-Brownian motion, and that the stochastic integrals $\int\sigma(y_i)\,dw$ under $\hat P$ have the law of $\int\sigma(X^i)\,dB^i$, which transfers the integral equation.

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, construction in the main theorem.
- N. Ikeda and S. Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland, 1989, <https://books.google.com/books?id=QZbOBQAAQBAJ>, exposition (topic).
- Wikipedia contributors, *Yamada–Watanabe theorem*, <https://en.wikipedia.org/wiki/Yamada%E2%80%93Watanabe_theorem>, Setting and Basic terminology.
