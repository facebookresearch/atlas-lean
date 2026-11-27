# Piecewise affine limit of log population sizes under power-law mutation

**Model.** Traits form the vertices $V$ of a finite directed graph $\mathcal G = (V,E)$; mutation is possible only along edges. Individuals of trait $v$ give birth at rate $b_v$, die at rate $d_v + \sum_w c^K_{v,w}N_w$ with competition $c^K_{v,w} = c_{v,w}/K$ ($c_{v,v}>0$), and each offspring is a mutant with probability $\mu_K = K^{-1/\alpha}$, $\alpha > 0$, its trait drawn from a kernel $m(v,\cdot)$ supported on out-neighbours. For a set $\mathbf v$ of coexisting resident traits with Lotka–Volterra equilibrium $\bar n(\mathbf v)$, the invasion fitness of $w$ is

$$f_{w,\mathbf v} = b_w - d_w - \sum_{v\in\mathbf v}c_{w,v}\,\bar n_v(\mathbf v),$$

and $d(\cdot,\cdot)$ denotes graph distance. Track the exponents $\beta^K_w(t) = \log\big(1 + N^K_w(t\log K)\big)/\log K$, so that $N^K_w \approx K^{\beta_w}$ on the time scale $\log K$.

**Theorem.** Assume $\alpha \notin \mathbb N$, $f_{w,\mathbf v} \ne 0$ for all $w$ and $\mathbf v$, and $\beta^K_w(0) \to (1 - d(\mathbf v_0,w)/\alpha)_+$ for an initial resident set $\mathbf v_0$ whose Lotka–Volterra system has a unique globally attractive positive equilibrium. Then $(\beta^K_w)_{w\in V}$ converges in probability, uniformly on $[0,T\wedge T_0]$, to a deterministic, continuous, piecewise affine function $\beta$ built inductively: with invasion times $s_0 = 0$ and $s_k = \inf\{t>s_{k-1} : \beta_w(t) = 1 \text{ for some non-resident } w\}$ (at which $w$ joins the residents $\mathbf v_k$), for $s_{k-1} \le t \le s_k$

$$\beta_w(t) = \max_{u \in V}\Big[\beta_u(s_{k-1}) + (t - t_{u,k}\wedge t)\,f_{u,\mathbf v_{k-1}} - \frac{d(u,w)}{\alpha}\Big] \vee 0,$$

where $t_{u,k}$ is the first time in $[s_{k-1},s_k]$ at which trait $u$ is present (when a neighbour reaches exponent $1/\alpha$). The construction stops at $T_0$ if two traits invade simultaneously, the new Lotka–Volterra system lacks a unique stable equilibrium, or a degenerate extinction occurs. Rescaled sizes $N^K_w(t\log K)/K$ then converge to the successive Lotka–Volterra equilibria between invasion times.

**Effective random walk across fitness valleys.** On longer time scales, valleys of unfit traits are crossed by rare mutant chains. For example, on $V = \{0,1a,1b,i\}$ with $\alpha \in (0,1)$, an unfit intermediate $i$ and fitness ordering $1a \gg 0 \gg 1b \gg 1a$, the population on the time scale $K^{-1+2/\alpha} = 1/(K\mu_K^2)$ converges (finite-dimensional distributions) to a Markov chain jumping between monomorphic states $0$ and $1b$ with explicit rates, e.g. $r_{0\to1b} = \frac{\bar n_0b_0}{|f_{i,0}|}\lambda(\rho_{i,0})\frac{f_{1a,0}}{b_{1a}}$, with $\lambda(\rho) = \sum_{k\ge1}\frac{(2k)!}{(k-1)!(k+1)!}\rho^k(1-\rho)^{k+1}$ and $\rho_{i,j} = b_i/(b_i + d_i + c_{ij}\bar n_j)$, even though $f_{1b,0} < 0$.

## Expansion

On the $\log K$ time scale a subpopulation of size $K^{\beta}$ with growth rate $f$ evolves like $K^{\beta + ft}$, so exponents move with slope equal to the invasion fitness against the current residents, while mutation from a trait at exponent $\beta_u$ feeds its neighbours at exponent $\beta_u - 1/\alpha$; the maximum in the formula selects the dominant source among growth and mutational influx. When a trait reaches exponent $1$ it becomes macroscopic, the residents' Lotka–Volterra system re-equilibrates in $O(1)$ time, and all slopes change. The comparison uses branching processes with immigration, whose log-size limits are piecewise linear.

## Sources

- Loren Coquille, Anna Kraut and Charline Smadi, "Stochastic individual-based models with power law mutation rate on a general finite trait space", arXiv:2003.03452 (2020), Theorem 2.2 (convergence of exponents), Proposition 2.3 (Lotka–Volterra equilibria), Theorems 3.2 and 3.3 (effective random walks on two and three sites), Corollary A.4 (branching processes with immigration), <https://doi.org/10.48550/arXiv.2003.03452>.
