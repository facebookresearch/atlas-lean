# Kurtz's diffusion approximation for density-dependent chains

Let $X^N$ be the density-dependent chains of [Kurtz's law of large numbers](kurtz-law-of-large-numbers-for-density-dependent.md), with finitely many jump directions $l\in\Lambda\subset\mathbb Z^d$, bounded rates $\beta_l$ and globally Lipschitz drift $F(x)=\sum_ll\,\beta_l(x)$, constructed from independent unit Poisson processes $Y_l$ as in the [random time-change representation](random-time-change-representation-of-density-dep.md). Let $x$ solve $\dot x=F(x)$, $x(0)=x_0$. Assume in addition:

- each $\beta_l$ is continuously differentiable with bounded derivatives, so that $F$ is $C^1$ with Jacobian $DF$;
- the initial fluctuations converge: $\sqrt N(X^N_0-x_0)\to V_0$ in distribution;
- $X^N_0$ is independent of $(Y_l)_l$.

Put $G(x)=\sum_{l\in\Lambda}l\,l^{\mathsf T}\beta_l(x)$, a positive semidefinite matrix, and let $W$ be a standard $d$-dimensional Brownian motion independent of $V_0$. Then, for every $T>0$,

$$\sqrt N\bigl(X^N-x\bigr)\Longrightarrow V\qquad\text{in distribution in }D([0,T],\mathbb R^d),$$

where $V$ is the unique solution of the linear stochastic differential equation

$$dV_t=DF(x(t))\,V_t\,dt+G(x(t))^{1/2}\,dW_t,\qquad V(0)=V_0 .$$

The limit $V$ is Gaussian when $V_0$ is Gaussian or deterministic; in general it is conditionally Gaussian given $V_0$. Convergence $X^N_0\to x_0$ alone is not sufficient: with all rates zero and $X^N_0=\lfloor N^{3/4}\rfloor/N$, one has $X^N_0\to0$ but $\sqrt N\,X^N_0\to\infty$, and $\sqrt N(X^N-x)$ has no limit. With the deterministic start $X^N_0=\lfloor Nx_0\rfloor/N$ (coordinatewise), $V_0=0$ and the limit is a centred Gaussian process.

## Depends on

- [Kurtz's law of large numbers for density-dependent chains](kurtz-law-of-large-numbers-for-density-dependent.md)
- [Random time-change representation of density-dependent chains](random-time-change-representation-of-density-dep.md)

## Proof depends on

- [Functional law of large numbers for the unit Poisson process](../../point-processes/poisson-processes/functional-lln-and-clt-for-the-unit-poisson-proc.md)

## Expansion

A full proof page must establish the following.

- The functional central limit theorem for the unit Poisson process, $(Y(Nu)-Nu)/\sqrt N\Rightarrow$ standard Brownian motion in $D[0,T]$ (a separate statement from the [functional law of large numbers for the unit Poisson process](../../point-processes/poisson-processes/functional-lln-and-clt-for-the-unit-poisson-proc.md)), applied jointly to the independent clocks and composed with the internal times $N\int_0^t\beta_l(X^N_s)ds$, which converge after division by $N$ by the law of large numbers.
- The linearization $\sqrt N\int_0^t(F(X^N_s)-F(x(s)))\,ds=\int_0^tDF(x(s))V^N_s\,ds+o(1)$ uniformly on $[0,T]$, using the $C^1$ hypothesis.
- Existence, uniqueness and the explicit solution $V_t=\Phi(t,0)V_0+\int_0^t\Phi(t,s)G(x(s))^{1/2}dW_s$ of the linear equation, with $\Phi$ the fundamental matrix of $\dot y=DF(x(t))y$, and continuity of the solution map, which gives convergence in distribution.
- Independence of $V_0$ and $W$ from the independence of $X^N_0$ and the clocks.
- The two guards above, and the linear birth–death example $\beta_1(x)=\lambda x$, $\beta_{-1}(x)=\mu x$, $\lambda\ne\mu$, $V_0=0$: $\operatorname{Var}V_t=\frac{\lambda+\mu}{\lambda-\mu}\,x_0\,e^{(\lambda-\mu)t}\bigl(e^{(\lambda-\mu)t}-1\bigr)$, which agrees with the exact variance of the linear birth–death process scaled by $N$. Its rates are unbounded, so it needs the version of the theorem localized to a neighbourhood of the trajectory.

## Sources

- T. G. Kurtz, *Approximation of Population Processes*, CBMS-NSF Regional Conference Series in Applied Mathematics 36, SIAM (1981), <https://books.google.com/books?id=DOl9i1uN6QEC>, diffusion approximation (statement and proof).
