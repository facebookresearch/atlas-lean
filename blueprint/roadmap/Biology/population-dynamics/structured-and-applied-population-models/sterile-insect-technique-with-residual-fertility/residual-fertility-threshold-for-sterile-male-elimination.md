# Residual-fertility threshold for sterile-male elimination

**Wild model.** Larvae $L$ (carrying capacity $K$), pupae $P$, males $M_W$, and single- and double-mated females $F_W,F_{WW}$ follow

$$\dot L=(b_WF_W+b_{WW}F_{WW})\Bigl(1-\frac LK\Bigr)-(\nu_L+\mu_L)L,\quad \dot P=\nu_LL-(\nu_P+\mu_P)P,\quad \dot M_W=(1-r)\nu_PP-\mu_MM_W,$$

$$\dot F_W=r\nu_PP-(\delta+\mu_F)F_W,\qquad \dot F_{WW}=\delta F_W-\mu_{F,WW}F_{WW},$$

with re-mating rate $\delta$. Its basic offspring number is

$$\mathcal R_W=\mathcal N_W\Bigl(1+\frac{b_{WW}}{b_W}\frac{\delta}{\mu_{F,WW}}\Bigr),\qquad \mathcal N(b,\delta,\mu)=\frac{rb}{\mu+\delta}\frac{\nu_L}{\nu_L+\mu_L}\frac{\nu_P}{\nu_P+\mu_P},\quad\mathcal N_W=\mathcal N(b_W,\delta,\mu_F).$$

If $\mathcal R_W\le 1$ the origin is globally asymptotically stable; if $\mathcal R_W>1$ the positive equilibrium with $L^*=(1-1/\mathcal R_W)K$ is globally asymptotically stable off the invariant set $\{L=P=F_W=F_{WW}=0\}$.

**Sterile releases.** Sterile males released at constant rate $\Lambda$ (stationary level $M_S^*=\Lambda/\mu_S$) mate with females with competitiveness weights, producing sterile-mated classes $F_S,F_{SS}$ (and mixed $F_{WS},F_{SW}$) whose fecundity is reduced by the residual fertility $\varepsilon\in[0,1]$. Define

$$\mathcal R_S=\mathcal N(b_S,\delta_S,\mu_{F,S})\Bigl(1+\frac{b_{SS}}{b_S}\frac{\delta_S}{\mu_{F,SS}}\Bigr).$$

**Theorem.** Assume $\mathcal R_W>1$.
1. If $\varepsilon\mathcal R_S<1$, the extinction equilibrium is locally asymptotically stable for every $\Lambda>0$ (a strong Allee effect), and there is a critical release rate $\Lambda^{crit}_{cont,\varepsilon}$ such that for $\Lambda>\Lambda^{crit}_{cont,\varepsilon}$ it is globally asymptotically stable.
2. If $\varepsilon\mathcal R_S>1$, the extinction equilibrium is unstable and a positive steady state exists whatever the release rate: elimination is impossible.
3. For periodic impulsive releases of size $\tau\Lambda_{per}$ every $\tau$ time units with $\varepsilon\mathcal R_S<1$, extinction is globally asymptotically stable when $\Lambda_{per}>\frac{e^{\mu_S\tau}-1}{\tau\mu_S}\Lambda^{U,crit}_{cont,\varepsilon}$ for an explicit constant $\Lambda^{U,crit}_{cont,\varepsilon}$, while if $0<\tau\Lambda_{per}\le\frac{1-e^{-\mu_S\tau}}{\mu_S}\Lambda^{crit}_{cont,\varepsilon}$ a positive $\tau$-periodic solution exists.

## Expansion

At the extinction state with releases, wild matings vanish and every female is sterile-mated, so the linearization is a cooperative system whose growth is governed by the offspring of sterile-mated females, $\varepsilon\mathcal R_S$; the threshold uses only larval, pupal and sterile-mated female parameters, and reduces without re-mating to $\varepsilon\mathcal N_{0,W}<1$. Above the critical release rate the wild population cannot sustain itself even from large densities, which gives global stability (proofs in the paper's appendices). Entomopathogenic fungi raise adult and pupal mortality, which lowers $\mathcal R_S$ and so raises the tolerable residual fertility $1/\mathcal R_S$.

## Sources

- Y. Dumont, "On the improvement of the sterile insect technique by entomopathogenic fungi: impact of residual fertility and re-mating behaviour", Bulletin of Mathematical Biology 87(10) (2025) 151, <https://doi.org/10.1007/s11538-025-01529-8>, PMCID PMC12443905. Systems (2)–(3), Theorem 1.3, Lemma 1.4, Proposition 1.10, Theorem 1.13, Proposition 2.2 and Theorem 2.4.
