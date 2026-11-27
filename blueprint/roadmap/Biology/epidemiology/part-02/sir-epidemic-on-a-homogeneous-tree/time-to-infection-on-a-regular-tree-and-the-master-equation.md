# Time to infection on a regular tree and the high-degree master equation

**Model.** Let $\mathcal T$ be the homogeneous tree in which every vertex has $n+1$ neighbors, $n\ge1$. At time $0$ each vertex is independently infected with probability $p$ and susceptible otherwise. A vertex infected for time $t$ transmits to each susceptible neighbor at rate $\varepsilon_t$ until it recovers after a random time $H$ (i.i.d. over vertices, absolutely continuous, discrete or mixed, possibly $H\equiv\infty$); a susceptible vertex is also infected from outside at rate $\lambda_t$. Assume $\varepsilon,\lambda$ bounded measurable. Define, for $t\ge0$ (and $=1$ for $t<0$),

$$
\varphi_t=\mathbb E\Bigl(e^{-\int_0^{t\wedge H}\varepsilon_u\,du}\Bigr),\qquad f_t=e^{-\int_0^t\lambda_u\,du},
$$

the probabilities that an infected vertex has not transmitted to a given neighbor by time $t$, and that a susceptible vertex has not been infected from outside by time $t$.

**Theorem (time to infection).** Let $\tau$ be the infection time of a given vertex ($\tau=0$ if initially infected). Then

$$
\mathbb P(\tau>t)=(1-p)\,f_t\,s_t^{\,n+1},\qquad t\ge0,
$$

where $s_t$ is the solution of the nonlinear integral equation

$$
s_t=\varphi_t-(1-p)\int_0^t f_u\,s_u^{\,n}\,\varphi'_{t-u}\,du .
$$

Here $s_t$ is the probability that the vertex receives no infection from one fixed neighbor by time $t$ (computed in the tree with the vertex removed). Special cases, with all vertices initially susceptible ($p=0$) and constants $\varepsilon,\lambda$: with exponential recovery at rate $\mu$, the equation is equivalent to the Bernoulli-type ODE $s'_t=-(\mu+\varepsilon)s_t+\varepsilon e^{-\lambda t}s_t^{\,n}+\mu$, $s_0=1$; with no recovery ($H\equiv\infty$) it is solved in closed form. For general $p$ the same differentiation gives $s'_t=-(\mu+\varepsilon)s_t+\varepsilon(1-p)e^{-\lambda t}s_t^{\,n}+\mu$.

**Theorem (high-degree limit).** Scale the transmission rate to $\varepsilon_t/(n+1)$, keeping $H$ and $\lambda$ fixed, and let $S_{t,n}=\mathbb P(\tau>t)$ be the expected susceptible fraction. Every pointwise limit point $S_t$ of $(S_{t,n})_n$ as $n\to\infty$ satisfies the **master equation**

$$
\log\frac{S_t}{S_0}=-\int_0^t\lambda_u\,du-\int_0^t\bigl(1-S_u\bigr)\gamma_{t-u}\,du,\qquad \gamma_t=\varepsilon_t\,\mathbb P(H>t),\quad S_0=1-p ,
$$

and the infected and recovered fractions are explicit functionals of $S$. For constant $\varepsilon$, exponential $H$ and $\lambda=0$ this is the integrated form of the Kermack–McKendrick SIR equations.

## Expansion

On a tree, the infection events arriving at a susceptible vertex $x$ through its $n+1$ neighbors are independent, because the subtrees hanging off $x$ are disjoint and $x$, while susceptible, transmits nothing. So $\mathbb P(\tau>t)$ factorizes as $(1-p)f_t$ times the $(n+1)$-st power of the probability $s_t$ that a given neighbor $y$ has not infected $x$. Either $y$ is never infected before $t$ (and then cannot transmit), or $y$ becomes infected at time $u$ (through its own $n$ other neighbors or from outside, which happens with density $-\frac{d}{du}[(1-p)f_us_u^n]$, plus an atom $p$ at $0$) and fails to transmit during $[u,t]$ with probability $\varphi_{t-u}$; integrating by parts gives the renewal equation. Under the scaling, $s_t^{\,n+1}\approx\exp\{-(n+1)(1-s_t)\}$ with $(n+1)(1-s_t)$ converging to $\int_0^t(1-S_u)\gamma_{t-u}du$, which gives the master equation.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Sources

- A. Gairat and V. Shcherbakov, "Discrete SIR model on a homogeneous tree and its continuous limit", arXiv:2005.04743 (2020), Section 2 (assumptions (A1)–(A2), definition of $\varphi$ and $f$, Theorem 1 on the time to infection), Section 3 (Theorem 2, continuous limit and master equation) and Section 5 (Appendix, Corollaries 1–3 for no recovery, constant and exponential recovery, stated for $p=0$), <https://doi.org/10.48550/arXiv.2005.04743>.
