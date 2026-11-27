# Piecewise affine limit of log population sizes under power-law mutation

**Model.** Traits form the vertices $V$ of a finite directed graph $\mathcal G = (V,E)$; mutation is possible only along edges. Individuals of trait $v$ give birth at rate $b_v$, die at rate $d_v + \sum_w c^K_{v,w}N_w$ with competition $c^K_{v,w} = c_{v,w}/K$ ($c_{v,v}>0$), and each offspring is a mutant with probability $\mu_K = K^{-1/\alpha}$, $\alpha > 0$, its trait drawn from a kernel $m(v,\cdot)$ supported on out-neighbours. For a set $\mathbf v$ of coexisting resident traits with Lotka–Volterra equilibrium $\bar n(\mathbf v)$, the invasion fitness of $w$ is

$$f_{w,\mathbf v} = b_w - d_w - \sum_{v\in\mathbf v}c_{w,v}\,\bar n_v(\mathbf v),$$

and $d(\cdot,\cdot)$ denotes graph distance. Track the exponents $\beta^K_w(t) = \log\big(1 + N^K_w(t\log K)\big)/\log K$, so that $N^K_w \approx K^{\beta_w}$ on the time scale $\log K$.

**Theorem.** Assume $\alpha \notin \mathbb N$, $f_{w,\mathbf v} \ne 0$ for every $\mathbf v \subseteq V$ and every trait $w$ that is not a resident of $\mathbf v$ (that is, $\bar n_w(\mathbf v) = 0$), and $\beta^K_w(0) \to (1 - d(\mathbf v_0,w)/\alpha)_+$ for an initial resident set $\mathbf v_0$ whose Lotka–Volterra system has a unique globally attractive positive equilibrium. Then $(\beta^K_w)_{w\in V}$ converges in probability, uniformly on $[0,T\wedge T_0]$, to a deterministic, continuous, piecewise affine function $\beta$ built inductively: with invasion times $s_0 = 0$ and $s_k = \inf\{t>s_{k-1} : \beta_w(t) = 1 \text{ for some non-resident } w\}$ (at which $w$ joins the residents $\mathbf v_k$), for $s_{k-1} \le t \le s_k$

$$\beta_w(t) = \max_{u \in V}\Big[\beta_u(s_{k-1}) + (t - t_{u,k}\wedge t)\,f_{u,\mathbf v_{k-1}} - \frac{d(u,w)}{\alpha}\Big] \vee 0,$$

where $t_{u,k}$ is the first time in $[s_{k-1},s_k]$ at which trait $u$ is present (when a neighbour reaches exponent $1/\alpha$). The construction stops and $T_0$ is set to $s_k$ if any of the following four cases occurs: (a) more than one non-resident trait $w\notin\mathbf v_{k-1}$ has $\beta_w(s_k) = 1$; (b) the mutation-free Lotka–Volterra system of $\mathbf v_k$, which includes $\mathbf v_{k-1}$ and the unique invading trait, does not have a unique globally attractive stable equilibrium; (c) some non-resident trait $w$ reaches exponent $0$ from above exactly at $s_k$ ($\beta_w(s_k) = 0$ and $\beta_w(s_k-\varepsilon) > 0$ for all small $\varepsilon > 0$); (d) some non-resident trait first appears exactly at $s_k$ ($s_k = t_{w,k}$). Rescaled sizes $N^K_w(t\log K)/K$ then converge to the successive Lotka–Volterra equilibria between invasion times.

## Expansion

On the $\log K$ time scale a subpopulation of size $K^{\beta}$ with growth rate $f$ evolves like $K^{\beta + ft}$, so exponents move with slope equal to the invasion fitness against the current residents, while mutation from a trait at exponent $\beta_u$ feeds its neighbours at exponent $\beta_u - 1/\alpha$; the maximum in the formula selects the dominant source among growth and mutational influx. When a trait reaches exponent $1$ it becomes macroscopic, the residents' Lotka–Volterra system re-equilibrates in $O(1)$ time, and all slopes change. The comparison uses branching processes with immigration, whose log-size limits are piecewise linear.

## Sources

- Loren Coquille, Anna Kraut and Charline Smadi, "Stochastic individual-based models with power law mutation rate on a general finite trait space", Electron. J. Probab. 26 (2021), paper no. 123, Assumptions 2.3–2.4, Theorem 2.7 (convergence of exponents, with the stopping time $T_0$ defined there) and Proposition 2.8 (Lotka–Volterra equilibria); preprint arXiv:2003.03452 (2020), Corollary A.4 (branching processes with immigration), <https://doi.org/10.48550/arXiv.2003.03452>.
