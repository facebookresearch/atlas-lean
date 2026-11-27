# Invasion thresholds for mutation- and plasmid-mediated resistance

**Model.** Within a host, a nutrient $B$ (supply $\Lambda$, washout $d$) feeds four bacterial strains $j\in\mathcal J=\{s,m,p,m.p\}$: sensitive ($s$), resistant by mutation ($m$), resistant by plasmid ($p$), and both ($m.p$). Strain $j$ consumes nutrient at rate $\beta_j$, converts with yield $\tau_j$, dies at rate $d_j$, mutates on division with probability $\varepsilon_j$, plasmid-bearing strains lose the plasmid on division with probability $\theta$, and plasmids are transferred by conjugation at rate $H(N)(N_p+N_{m.p})$ with a Beddington–DeAngelis function $H$ of the total population $N$:

$$
\begin{aligned}
\dot B&=\Lambda-dB-B\textstyle\sum_j\beta_jN_j,\\
\dot N_s&=\tau_s\beta_s(1-\varepsilon_s)BN_s-d_sN_s+\varepsilon_m\tau_m\beta_mBN_m+\theta\tau_p\beta_pBN_p-H(N)N_s(N_p+N_{m.p}),\\
\dot N_m&=\tau_m\beta_m(1-\varepsilon_m)BN_m-d_mN_m+\varepsilon_s\tau_s\beta_sBN_s+\theta\tau_{m.p}\beta_{m.p}BN_{m.p}-H(N)N_m(N_p+N_{m.p}),\\
\dot N_p&=\tau_p\beta_p(1-\theta)(1-\varepsilon_p)BN_p-d_pN_p+\varepsilon_{m.p}(1-\theta)\tau_{m.p}\beta_{m.p}BN_{m.p}+H(N)N_s(N_p+N_{m.p}),\\
\dot N_{m.p}&=\tau_{m.p}\beta_{m.p}(1-\theta)(1-\varepsilon_{m.p})BN_{m.p}-d_{m.p}N_{m.p}+\varepsilon_p(1-\theta)\tau_p\beta_pBN_p+H(N)N_m(N_p+N_{m.p}).
\end{aligned}
$$

With $B_0=\Lambda/d$ the bacteria-free nutrient level, define the growth thresholds $\mathcal T_j=B_0\tau_j\beta_j/d_j$ and

$$
\mathcal R_s=\mathcal T_s(1-\varepsilon_s),\quad \mathcal R_m=\mathcal T_m(1-\varepsilon_m),\quad \mathcal R_p=\mathcal T_p(1-\varepsilon_p)(1-\theta),\quad \mathcal R_{m.p}=\mathcal T_{m.p}(1-\varepsilon_{m.p})(1-\theta).
$$

**Theorem.** Assume the mutation probabilities $\varepsilon_j$ are sufficiently small, and set $\mathcal T^*=\max_j\mathcal T_j$, $\mathcal R^*=\max_j\mathcal R_j$. Then:
1. the bacteria-free state $E^0=(B_0,0,0,0,0)$ is locally asymptotically stable if $\mathcal R^*<1$ and unstable if $\mathcal R^*>1$;
2. $E^0$ is globally asymptotically stable if $\mathcal T^*<1$;
3. if $\min_j\mathcal T_j>1$, the system is uniformly persistent: there is $\delta>0$ such that every solution starting with some bacteria satisfies $\liminf_{t\to\infty}\operatorname{dist}(E(t),\partial X_0)\ge\delta$, where $\partial X_0$ is the bacteria-free boundary.

Solutions are nonnegative, bounded and unique, and the bacteria-free and bacteria-present sets are positively invariant.

## Expansion

At $E^0$ the conjugation terms vanish to first order (they are quadratic in the $N_j$), so the linearization splits into a plasmid-free block $(N_s,N_m)$ and a plasmid block $(N_p,N_{m.p})$ coupled only through segregational loss. Each block is a $2\times2$ Metzler matrix whose principal eigenvalue, for small mutation rates, is close to $\max(B_0\tau_j\beta_j(1-\varepsilon_j)\cdots-d_j)$, giving the threshold $\mathcal R^*$. Since $B(t)\le B_0$ eventually, each strain's per-capita growth is at most $B_0\tau_j\beta_j-d_j$; if $\mathcal T^*<1$ all strains decay, which is global extinction. Persistence follows from acyclicity of the boundary flow and the instability of $E^0$ in every strain direction.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- Ramsès Djidjou-Demasse, Samuel Alizon, Mircea T. Sofonea, "Within-host bacterial growth dynamics with both mutation and horizontal gene transfer", arXiv:2003.03083: Section 2 (model), Section 3: Theorem 3.1, Lemma 3.2 and Theorem 3.3 (invasion and threshold dynamics); proofs in Sections 7–8. <https://doi.org/10.48550/arXiv.2003.03083>
