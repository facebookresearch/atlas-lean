# PDE limit of the infection-age measure in a varying-infectivity SIR epidemic

**Model.** A homogeneous population of size $N$ is split into susceptible, infectious and recovered individuals, $N = S^N(t) + I^N(t) + R^N(t)$. Each infected individual $i$ carries a random infectivity function $\lambda_i(\cdot) \ge 0$ of its infection age. The functions are i.i.d., with mean $\bar\lambda(t) = \mathbb E[\lambda_1(t)]$ and infectious period $\eta_i = \sup\{t > 0 : \lambda_i(t) > 0\}$ with distribution function $F$, density $f$, survival function $F^c = 1 - F$ and hazard $h = f/F^c$. The measure-valued process $\mu^N_t(d\mathfrak a)$ records the infection ages of the currently infected, so $I^N(t) = \langle \mu^N_t, 1\rangle$. New infections occur at rate $\Upsilon^N(t) = \frac{S^N(t)}{N}\mathfrak F^N(t)$, where $\mathfrak F^N(t)$ is the total current infectivity. Initially infected individuals have i.i.d. ages with law $\bar\mu_0/\bar\mu_0(1)$.

**Assumption.** $\bar\mu_0(\{0\}) = 0$, $\bar\mu_0$ has compact support in $[0, \bar{\mathfrak a}]$, and $\bar\mu_0(1) < 1$. The initial fractions are $\bar S(0), \bar I(0) = \bar\mu_0(1), \bar R(0)$, summing to one.

**Theorem (functional law of large numbers).** If $h$ is locally bounded, then $(\bar S^N, \bar{\mathfrak F}^N) = N^{-1}(S^N, \mathfrak F^N)$ converges in probability in $D^2$ to the unique solution of the Volterra system

$$\bar S(t) = \bar S(0) - \int_0^t \bar\Upsilon(s)\,ds, \qquad \bar{\mathfrak F}(t) = \int_0^\infty \bar\lambda(\mathfrak a + t)\,\bar\mu_0(d\mathfrak a) + \int_0^t \bar\lambda(t-s)\,\bar\Upsilon(s)\,ds, \qquad \bar\Upsilon = \bar S\,\bar{\mathfrak F}.$$

Moreover $\bar\mu^N = N^{-1}\mu^N \Rightarrow \bar\mu$ in $D(\mathbb R_+, \mathcal M_F(\mathbb R_+))$. The limit $\bar\mu$ is the unique solution of the linear transport PDE with boundary input $\bar\Upsilon$,

$$\partial_t\bar\mu + \partial_{\mathfrak a}\bar\mu = -h\,\bar\mu, \qquad \bar\mu(t, 0) = \bar\Upsilon(t), \qquad \bar\mu(0,\cdot) = \bar\mu_0,$$

understood weakly against $\varphi \in C^1_c(\mathbb R_+)$, and it is given explicitly by

$$\bar\mu(t, d\mathfrak a) = \mathbf 1_{\mathfrak a < t}\,F^c(\mathfrak a)\,\bar\Upsilon(t - \mathfrak a)\,d\mathfrak a + \mathbf 1_{\mathfrak a \ge t}\,\frac{F^c(\mathfrak a)}{F^c(\mathfrak a - t)}\,\bar\mu_0(d\mathfrak a - t).$$

Consequently

$$\bar I(t) = \int_0^\infty \frac{F^c(t + \mathfrak a)}{F^c(\mathfrak a)}\,\bar\mu_0(d\mathfrak a) + \int_0^t F^c(t-s)\,\bar\Upsilon(s)\,ds,$$

and $\bar R = 1 - \bar S - \bar I$.

## Expansion

Integrating a test function against $\mu^N_t$ shows three effects: ages shift by $t$, new infections enter at age $0$ at rate $\Upsilon^N$, and recoveries remove mass at rate $h$. The martingale terms are $O(N^{-1/2})$, so the limit solves $\frac{d}{dt}\langle\bar\mu_t, \varphi\rangle = \varphi(0)\bar\Upsilon(t) + \langle\bar\mu_t, \varphi' - h\varphi\rangle$. A generic first-order PDE $\partial_t u + \partial_{\mathfrak a}u = -hu + g$ with $u(t,0) = k(t)$ has the unique explicit solution obtained by following characteristics. Mass entering at time $s$ survives to age $\mathfrak a$ with probability $F^c(\mathfrak a)$, and initial mass at age $\mathfrak a_0$ survives with conditional probability $F^c(\mathfrak a_0 + t)/F^c(\mathfrak a_0)$. Uniqueness follows by duality. The scalar closure $(\bar S, \bar{\mathfrak F})$ decouples from the PDE, so the PDE is linear once $\bar\Upsilon$ is known.

## Sources

- Guodong Pang and Etienne Pardoux, "SPDE for stochastic SIR epidemic models with infection-age dependent infectivity", Stochastics and Partial Differential Equations: Analysis and Computations 14 (2025), 776–829, <https://doi.org/10.1007/s40072-025-00403-x>; numbering as in arXiv:2410.17200: Section 2.1, Assumption 2.1, Section 2.2 (the generic linear first-order PDE), Theorem 2.1.
