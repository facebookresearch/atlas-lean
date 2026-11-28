# Host-state dynamics of a two-type parasite under balancing selection and reinfection

**Model.** $M$ hosts each carry $N$ parasites of types $A$ and $B$; $X_i\in\{0,\frac1N,\dots,1\}$ is the type-$A$ frequency in host $i$ and $\bar x=\frac1M\sum_jX_j$. Within a host, parasites follow Moran dynamics at rate $g_N$ with balancing selection towards a frequency $\eta\in(0,1)$; reinfection transmits a single parasite from a random host at rate $r_N$ per host, replacing a random parasite; a dying host (rate $1$) is replaced by a new host infected with a single type drawn from a random host. Thus $X_i$ jumps by $+\frac1N$ at rate $g_N(1+s_N(\eta-x_i))Nx_i(1-x_i)+r_N\bar x(1-x_i)$, by $-\frac1N$ at rate $g_N(1+s_N(x_i-\eta))Nx_i(1-x_i)+r_N(1-\bar x)x_i$, to $1$ at rate $\bar x$ and to $0$ at rate $1-\bar x$.

**Assumptions.** Moderate selection $s_N=N^{-b}$ with $b\in(0,1)$; frequent reinfection $r_Ns_N\to r>0$; fast parasite reproduction, $1/g_N=o(N^{-3b-\epsilon})$ and $g_N=O(\exp(N^{1-b(1+\epsilon)}))$.

**Theorem (large parasite populations, fixed $M$).** If the initial states concentrate on $\{0\}\cup[\alpha,1-\alpha]\cup\{1\}$, then as $N\to\infty$ the host states converge to a Markov chain $\mathbf Y^M$ on $\{0,\eta,1\}^M$: a mixed host is effectively at the balanced frequency $\eta$, a pure host becomes mixed when a successful reinfection by the other type occurs (probability of order $2s_N\eta$ or $2s_N(1-\eta)$ per reinfection, so at rate of order $r$), and host replacement resets hosts to $0$ or $1$.

**Theorem (propagation of chaos).** As $M\to\infty$ with exchangeable initial states (and also jointly with $M=M_N\to\infty$), any $k$ host paths converge to $k$ independent copies of a $\{0,\eta,1\}$-valued process $V$, and the host-state proportions $(Z^0,Z^\eta,Z^1)$ converge to the solution of

$$\begin{aligned} \dot v^0&=(1-\eta)v^\eta-2r\eta\,v^0\big(v^1+\eta v^\eta\big),\\ \dot v^\eta&=-v^\eta+2r\big(\eta^2v^0v^\eta+(1-\eta)^2v^1v^\eta+v^0v^1\big),\\ \dot v^1&=\eta v^\eta-2r(1-\eta)\,v^1\big(v^0+(1-\eta)v^\eta\big), \end{aligned}$$

which leaves the simplex $\Delta^3$ invariant.

## Expansion

A single transmitted parasite of the minority type escapes loss and reaches the balanced frequency $\eta$ with probability $\approx2s_N\eta$ (resp. $2s_N(1-\eta)$), by a gambler's-ruin estimate for the within-host birth–death chain with selective drift $s_N(\eta-x)$. Since reinfections occur at rate $r_N\approx r/s_N$, successful conversions of pure hosts happen at rate of order $r$ per host. Fast within-host reproduction makes balancing and resolution instantaneous on the host time scale, and host replacement at rate $1$ splits a mixed host into pure ones with probabilities $\eta$ and $1-\eta$ (the $(1-\eta)v^\eta$ and $\eta v^\eta$ terms). The process $V$ has a tree representation: $v_t^\ell$ equals the probability that a random genealogical branching-and-coalescing structure carries type $\ell$ at time $t$.

## Sources

- Cornelia Pokalyuk and Anton Wakolbinger, "Maintenance of diversity in a hierarchical host–parasite model with balancing selection and reinfection", *Stochastic Process. Appl.* 130(2) (2020), 1119–1158. <https://doi.org/10.1016/j.spa.2019.04.009>
- Preprint version (the locators in this item follow its numbering): Cornelia Pokalyuk, Anton Wakolbinger, "Maintenance of diversity in a hierarchical host-parasite model with balancing selection and reinfection", arXiv:1802.02429: Section 2.1 (model and Assumptions $(\mathcal A)$), Theorem 1 (fixed $M$), Proposition 2.7 and Corollary 2.8 (propagation of chaos as $M\to\infty$), Theorem 2 and Corollary 2.10 (joint limit), Lemma 3.3 and Corollary 3.4 (tree representation), Lemma 3.6 (probability to balance). <https://doi.org/10.48550/arXiv.1802.02429>
