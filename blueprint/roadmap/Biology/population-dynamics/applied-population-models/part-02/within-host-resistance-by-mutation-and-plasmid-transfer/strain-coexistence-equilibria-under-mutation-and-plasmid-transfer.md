# Strain coexistence equilibria under mutation and plasmid transfer

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

Define the strain transition numbers $\mathcal K_{s\to m}=B_0\varepsilon_s\tau_s\beta_s/d_m$, $\mathcal K_{m\to s}=B_0\varepsilon_m\tau_m\beta_m/d_s$, and analogously $\mathcal K_{p\to m.p}$, $\mathcal K_{m.p\to p}$ (with the factor $1-\theta$).

**Theorem (plasmid-free coexistence).** Let $r(D^{-1}G)$ be the principal eigenvalue of the plasmid-free next-generation matrix, so that

$$
\frac{1}{B^*}=r(D^{-1}G)=\frac{1}{2B_0}\Big\{\mathcal R_s+\mathcal R_m+\big[(\mathcal R_s-\mathcal R_m)^2+4\mathcal K_{m\to s}\mathcal K_{s\to m}\big]^{1/2}\Big\}.
$$

If $B_0r(D^{-1}G)>1$, there is a coexistence state $E^*_{s-m}=(B^*,N_s^*,N_m^*,0,0)$ with $(N_s^*,N_m^*)$ proportional to the Perron vector $\phi_0=\big(\mathcal R_s-\mathcal R_m+[(\mathcal R_s-\mathcal R_m)^2+4\mathcal K_{m\to s}\mathcal K_{s\to m}]^{1/2},\,2\mathcal K_{s\to m}\big)$. If the plasmid block has the larger principal eigenvalue and the conjugation flux $\alpha$ is small, a full coexistence state $E^*$ with all four strains exists and depends smoothly on $\alpha$.

**Theorem (stability classification).** For small mutation probabilities and small conjugation flux:
1. if $\max(\mathcal R_p,\mathcal R_{m.p})>1>\max(\mathcal R_s,\mathcal R_m)$, the only states are $E^0$ (unstable) and $E^*$ (locally asymptotically stable);
2. if $\max(\mathcal R_p,\mathcal R_{m.p})>\max(\mathcal R_s,\mathcal R_m)>1$, the states are $E^0$ and $E^*_{s-m}$ (both unstable) and $E^*$ (locally asymptotically stable);
3. if $\max(\mathcal R_s,\mathcal R_m)>1$ and $\max(\mathcal R_s,\mathcal R_m)>\max(\mathcal R_p,\mathcal R_{m.p})$, the states are $E^0$ (unstable) and $E^*_{s-m}$, which is locally asymptotically stable provided $\mathcal R_p/\max(\mathcal R_s,\mathcal R_m)$ and $\mathcal R_{m.p}/\max(\mathcal R_s,\mathcal R_m)$ plus the respective conjugation gains at $E^*_{s-m}$ stay below $1$.

## Expansion

At a plasmid-free state the nutrient level is set by the dominant plasmid-free lineage, $B^*=1/r(D^{-1}G)$, exactly as in a chemostat where the best competitor drives the resource to its break-even level. Plasmid-bearing strains can then invade iff their own threshold evaluated at $B^*$, plus the conjugation gain from the sensitive pool, exceeds one; this is the condition in item 3. When the plasmid block wins, perturbation in the small conjugation flux $\alpha$ continues the plasmid-only state into $E^*$, with plasmid-free strains maintained by segregational loss. The analysis predicts when plasmid-borne resistance outcompetes mutational resistance within a host.

## Depends on

- [Invasion thresholds for mutation- and plasmid-mediated resistance](invasion-thresholds-for-mutation-and-plasmid-resistance.md)
- [Basic reproduction number of the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Sources

- Ramsès Djidjou-Demasse, Samuel Alizon, Mircea T. Sofonea, "Within-host bacterial growth dynamics with both mutation and horizontal gene transfer", arXiv:2003.03083: Section 3 (strain transition numbers); Section 4: Theorem 4.1 (nontrivial stationary states) and Theorem 4.2 (stability results). <https://doi.org/10.48550/arXiv.2003.03083>
