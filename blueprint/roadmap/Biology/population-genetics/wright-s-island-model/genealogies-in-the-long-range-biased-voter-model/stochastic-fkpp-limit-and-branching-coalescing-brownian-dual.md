# Stochastic Fisher–KPP limit of the long-range biased voter model and its branching–coalescing Brownian dual

**Model.** On $\Lambda_n=(L_n^{-1}\mathbb Z)\times\{1,\dots,M_n\}$ each site carries one cell of type $0$ or $1$; the $M_n$ cells of deme $w$ interact only with the $2M_n$ cells of demes $w\pm L_n^{-1}$. Type-$0$ cells reproduce at rate $2M_nr_n$ and type-$1$ cells at rate $2M_n(r_n+\theta R_n^{-1})$, $\theta\ge0$; the offspring replaces a uniformly chosen neighbor (birth–death updating). This one-dimensional model of an expanding population (after Hallatschek and Nelson) has local density $u^n_t(w)=M_n^{-1}\sum_{i\le M_n}\xi_t(w,i)$, linearly interpolated between demes.

**Theorem (scaling limit).** Suppose $u^n_0\to f_0$ in $C_b(\mathbb R)$ (topology of uniform convergence on compacts) and

$$\alpha_n=\frac{r_nM_n}{L_n^2}\to\alpha\in(0,\infty),\qquad \beta_n=\frac{M_n}{R_n}\to\beta\in[0,\infty),\qquad \gamma_n=\frac{r_n}{L_n}\to\gamma\in[0,\infty),$$

with $L_n\to\infty$ and $L_nR_n\to\infty$. Then $u^n$ converges in distribution in $D([0,\infty),C_b(\mathbb R))$ to the continuous weak solution of the stochastic Fisher–KPP (Wright–Fisher) equation

$$\partial_tu=\alpha\,\Delta u+2\theta\beta\,u(1-u)+\sqrt{4\gamma\,u(1-u)}\;\dot W,\qquad u_0=f_0,$$

with $\dot W$ space-time white noise.

**Theorem (dual and genealogies).** Under the same scaling, the dual branching–coalescing random walk of the biased voter model converges to a system of particles performing independent Brownian motions with variance $2\alpha t$, branching at rate $\theta\beta$, in which each pair coalesces when the local time at $0$ of the difference of their positions exceeds $\alpha\tau/\gamma$, $\tau$ an independent mean-one exponential (no coalescence if $\gamma=0$). In particular (neutral stepping-stone case), for two lineages sampled from colonies at distance $L$ with colony size $M$ and migration rate $\nu$, if $L\to\infty$ and $M\nu/L\to\alpha$, then the coalescence time $t_0$ satisfies

$$\frac{2t_0}{L^2/\nu}\ \Rightarrow\ \ell_0^{-1}(\alpha\tau),$$

where $\ell_0$ is the local time at $0$ of a standard Brownian motion started at $1$. Coalescences in the limit are binary: there are no simultaneous mergers, in contrast with the Bolthausen–Sznitman genealogies conjectured for pulled fronts.

## Expansion

The density limit is a generalization of Mueller and Tribe's long-range voter model result: the drift of $u^n$ is a discrete Laplacian (scaled by $\alpha_n$) plus the selective bias, whose net effect per unit time is $2\theta\beta_n u(1-u)$, and the quadratic variation of the resampling martingale, of order $r_n/L_n$ per unit space, gives the Wright–Fisher noise $4\gamma u(1-u)$. Tightness and the identification of the martingale problem yield convergence, and uniqueness in law follows from duality. In Harris's graphical representation, tracing back from a cell gives a branching–coalescing random walk (branching at selective arrows that point from a type-$1$ candidate); two lineages in the same deme coalesce at rate of order $r_n/M_n$, and they spend time of order $L_n^{-1}$ per unit local time together, so coalescence is triggered by an exponential amount of rescaled intersection local time.

## Sources

- Rick Durrett, Wai-Tong (Louis) Fan, "Genealogies in expanding populations", *The Annals of Applied Probability* 26 (2016), 3456–3490, <https://doi.org/10.1214/16-AAP1181>; preprint arXiv:1507.00918, <https://doi.org/10.48550/arXiv.1507.00918>. Numbering of the arXiv version: Section 1 (model; Lemma 1 duality; Theorems 1, 2 and 3).
