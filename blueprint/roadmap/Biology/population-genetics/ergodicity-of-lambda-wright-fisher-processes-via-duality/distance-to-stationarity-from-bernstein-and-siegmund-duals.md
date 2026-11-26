# Distance to stationarity from Bernstein and Siegmund duals

**Dualities.** Let $X$ be a Markov process on $[0,1]$. A Markov process $V$ on $\bigcup_{n\ge0}\mathbb{R}^{n+1}$ is a **Bernstein dual** of $X$ if, with $L_t=\dim(V_t)-1$ and $H(x,w)=\sum_{i=0}^{\dim w-1}w_i\binom{\dim w-1}{i}x^i(1-x)^{\dim w-1-i}$ (a polynomial in Bernstein form),
$$
\mathbb{E}_x[H(X_t,v)]=\mathbb{E}_v[H(x,V_t)]\qquad\text{for all }x\in[0,1],\ v,\ t\ge0 .
$$
A process $Y$ on $[0,1]$ is a **Siegmund dual** of $X$ if $\mathbb{P}_x(X_t\ge y)=\mathbb{P}_y(x\ge Y_t)$ for all $x,y,t$. Write $\rho^X_{x,t}$ for the law of $X_t$ under $\mathbb{P}_x$, $W_p$ for Wasserstein distances and $d_{\mathrm{Rad}}$ for the Radon (total-variation type) distance.

**Theorem (Bernstein dual case; Cordero–Véchambre, Theorem 2.8).** Suppose $X$ has a Bernstein dual $V$ with the structural property $V_t=C_tv$ for random linear maps $C_t$ of operator sup-norm at most $1$ (frozen once $L$ hits $0$), and the length process $L_t$ is absorbed at $0$ in finite time almost surely. Then $X$ has a stationary law $\rho^X_\infty$, is $W_1$-uniformly ergodic on $[0,1]$, and for all $t\ge0$, $n\ge1$,
$$
2\sup_{x}W_1(\rho^X_{x,t},\rho^X_\infty)\le\sup_xd_{\mathrm{Rad}}(\rho^X_{x,t},\rho^X_\infty)\le 2\sup_{n\ge1}\mathbb{P}_n(L_t\ne0),\qquad
\sup_xW_1(\rho^X_{x,t},\rho^X_\infty)\le\frac{1}{\sqrt n}+\mathbb{P}_n(L_t\ne0).
$$

**Theorem (Siegmund dual case; Theorem 2.9).** Suppose $X$ admits a monotone coupling (for $x_1\le x_2$, $\mathbb{P}_{x_1,x_2}(X^1_t<y\le X^2_t)=\mathbb{P}_y(x_1<Y_t\le x_2)$) and a Siegmund dual $Y$ that is regularly absorbed ($\mathbb{P}_z(Y_\infty=1)\to1$ as $z\to1$, $\mathbb{P}_z(Y_\infty=0)\to1$ as $z\to0$) and uniformly absorbed ($\sup_z\mathbb{P}_z(Y_t\in[\epsilon,1-\epsilon])\to0$) in $\{0,1\}$. Then $\rho^X_\infty(\{0,1\})=0$, $X$ is locally $W_p$-uniformly ergodic on $(0,1)$ for every $p\ge1$, and for $\epsilon\in(0,1/2)$,
$$
\sup_{x\in[\epsilon,1-\epsilon]}W_p(\rho^X_{x,t},\rho^X_\infty)^p\le\sup_{y}\mathbb{P}_y\big(Y_t\in[\epsilon,1-\epsilon]\big)+\mathbb{P}_\epsilon(Y_\infty=1)+\mathbb{P}_{1-\epsilon}(Y_\infty=0).
$$

**From ergodicity to recurrence (Propositions 2.11–2.12).** If $X$ is uniformly ergodic in the Lévy–Prokhorov metric on $[0,1]$, or locally uniformly ergodic on $(0,1)$ with $\rho^X_\infty(\{0,1\})=0$, then every point of $\operatorname{supp}\rho^X_\infty$ is topologically recurrent: each of its neighbourhoods is visited at arbitrarily large times almost surely from any start in $(0,1)$.

## Expansion

Both bounds turn a coupling problem for two trajectories of $X$ into an absorption problem for one trajectory of the dual. For the Bernstein dual, once $L_t=0$ the right side of the duality no longer depends on $x$, so all starting points give the same expectation of every Bernstein polynomial; Bernstein polynomials of degree $n$ approximate Lipschitz test functions within $1/(2\sqrt n)$, which gives the $W_1$ bound. For the Siegmund dual, the difference of distribution functions from two starting points equals the probability that $Y$ has not yet decided between $0$ and $1$.

## Sources

- F. Cordero, G. Véchambre, "Distance to stationarity and open set recurrence for ergodic processes on the unit interval with a Bernstein or a Siegmund dual", arXiv:2507.07587 (2025). <https://doi.org/10.48550/arXiv.2507.07587>
