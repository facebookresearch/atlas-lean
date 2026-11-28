# Propagation of chaos for mean-field interacting multitype birth–death processes

**Model.** Consider $N$ lineages (e.g. B-cell families in a germinal centre, or clades), lineage $j$ having state $\mathbf z_j\in\mathbb N_0^D$, the numbers of particles of each of $D$ types. Let $\pi_{\mathbf z}=\frac1N\sum_j\delta_{\mathbf z_j}$ be the empirical distribution of lineage states. Within lineage $j$, a type-$i$ particle is born at rate $b^i(\mathbf z_j,\pi_{\mathbf z})$, dies at rate $d^i(\mathbf z_j,\pi_{\mathbf z})$ and mutates to type $k$ at rate $m^{i,k}(\mathbf z_j,\pi_{\mathbf z})$ (all zero if $z_{j,i}=0$), so interactions are strong within a lineage (e.g. carrying capacity) and weak, through $\pi$, between lineages (e.g. competition for a shared resource or frequency-dependent selection). Assume linear growth, $b^i,d^i,m^{i,k}\le L(\|\mathbf y\|_1+1)$, and Lipschitz continuity $|b^i(\mathbf y,\nu)-b^i(\mathbf y',\nu')|\le L(\|\mathbf y-\mathbf y'\|_1+\|\nu-\nu'\|_{TV})$, and likewise for $d^i,m^{i,k}$.

**Theorem.** If the initial lineages are exchangeable with empirical law $\nu^N\to\nu$, then the empirical measure process $\Pi^N(t)=\pi_{\mathbf Z^N(t)}$ converges in distribution to the deterministic path $v(t)$, the unique solution of the nonlinear Kolmogorov forward system

$$v'_{\{\mathbf y\}}=-v_{\{\mathbf y\}}\sum_i\Big(b^i(\mathbf y,v)+d^i(\mathbf y,v)+\sum_{k\ne i}m^{i,k}(\mathbf y,v)\Big)+\sum_i\Big(v_{\{\mathbf y-e_i\}}b^i(\mathbf y-e_i,v)+v_{\{\mathbf y+e_i\}}d^i(\mathbf y+e_i,v)+\sum_{k\ne i}v_{\{\mathbf y-e_k+e_i\}}m^{i,k}(\mathbf y-e_k+e_i,v)\Big),$$

$v(0)=\nu$. Moreover, for each fixed $k$, the first $k$ lineages converge jointly to $k$ **independent** copies of a time-inhomogeneous, non-interacting multitype birth–death process with rates $b^i(\cdot,v(t))$, $d^i(\cdot,v(t))$, $m^{i,\ell}(\cdot,v(t))$.

## Expansion

Each lineage interacts with the others only through the empirical measure, so as $N\to\infty$ the law of large numbers replaces $\pi$ by the deterministic flow $v$, and lineages decouple (propagation of chaos). Because rates are unbounded in lineage size, the proof first freezes lineages above a size $\kappa$, proves convergence for the truncated system, and shows the truncation error is small uniformly in $N$. The consequence for phylodynamics is that a single sampled lineage evolves as a linear multitype birth–death process with time-varying rates set by the population-level field $v(t)$, so the standard message-passing (pruning) likelihood of a typed tree remains available, while the time variation encodes interactions such as density dependence or competition that linear phylogenetic birth–death models exclude.

## Sources

- William S. DeWitt, Steven N. Evans, Ella Hiesmayr and Sebastian Hummel, "Mean-field interacting multi-type birth–death processes with a view to applications in phylodynamics", Theoretical Population Biology 159 (2024), 1–12, <https://doi.org/10.1016/j.tpb.2024.07.002>; numbering as in arXiv:2307.06010: Section 2 (Assumption 2.1, Propositions 2.3–2.4, Theorem 2.5, Corollary 2.7) and Section 3 (truncation, Propositions 3.5 onward).
