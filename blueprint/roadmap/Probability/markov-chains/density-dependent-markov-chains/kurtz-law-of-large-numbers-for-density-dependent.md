# Kurtz's law of large numbers for density-dependent chains

Let $X^N$ be the density-dependent chains of the [random time-change representation](random-time-change-representation-of-density-dep.md): finitely many jump directions $l\in\Lambda\subset\mathbb Z^d$, bounded continuous rates $\beta_l$, and

$$X^N_t=X^N_0+\sum_{l\in\Lambda}\frac lN\,Y_l\!\left(N\int_0^t\beta_l(X^N_s)\,ds\right).$$

Assume that the drift $F(x)=\sum_{l\in\Lambda}l\,\beta_l(x)$ is globally Lipschitz on $\mathbb R^d$, and let $x$ be the unique solution of $\dot x(t)=F(x(t))$, $x(0)=x_0$. If $X^N_0\to x_0$ in probability as $N\to\infty$, then for every $T>0$

$$\sup_{0\le t\le T}\bigl|X^N_t-x(t)\bigr|\longrightarrow0\qquad\text{in probability}.$$

Example (selection in a large Moran population): for $d=1$, $\Lambda=\{1,-1\}$, $\beta_1(x)=(1+s)x(1-x)$ and $\beta_{-1}(x)=x(1-x)$ on $[0,1]$, so that $NX^N$ counts the favoured type in a population of size $N$ in which the favoured type reproduces at rate $1+s$ and every birth replaces a uniformly chosen individual, the limit is the logistic equation $\dot x=s\,x(1-x)$.

## Depends on

- [Random time-change representation of density-dependent chains](random-time-change-representation-of-density-dep.md)
- [Global existence and uniqueness for globally Lipschitz ODEs](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)

## Proof depends on

- [Functional law of large numbers for the unit Poisson process](../../point-processes/poisson-processes/functional-lln-and-clt-for-the-unit-poisson-proc.md)
- [Gronwall inequality (integral form)](../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Expansion

A full proof page must establish the following.

- The decomposition $X^N_t=X^N_0+\sum_l\frac lN\tilde Y_l\bigl(N\int_0^t\beta_l(X^N_s)ds\bigr)+\int_0^tF(X^N_s)\,ds$ with the centred processes $\tilde Y_l(u)=Y_l(u)-u$.
- Since the internal times are at most $NT\sup\beta_l$, the [functional law of large numbers for the unit Poisson process](../../point-processes/poisson-processes/functional-lln-and-clt-for-the-unit-poisson-proc.md) makes the martingale terms tend to zero uniformly on $[0,T]$ almost surely.
- Gronwall's inequality with the Lipschitz constant of $F$ then bounds $\sup_{t\le T}|X^N_t-x(t)|$ by $(|X^N_0-x_0|+\varepsilon_N)e^{\mathrm{Lip}(F)T}$ with $\varepsilon_N\to0$.
- The Moran example: compute $F(x)=s\,x(1-x)$; the rates are given on $[0,1]$ and are extended to bounded continuous functions with Lipschitz drift outside it, which does not affect the chain started in $[0,1]$.

## Sources

- T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump Markov processes* (1970), <https://cir.nii.ac.jp/crid/1360579815925645568>, law of large numbers for pure jump processes (statement and proof).
- T. G. Kurtz, *Approximation of Population Processes*, CBMS-NSF Regional Conference Series in Applied Mathematics 36, SIAM (1981), <https://books.google.com/books?id=DOl9i1uN6QEC>, chapter on the law of large numbers (statement and proof).
