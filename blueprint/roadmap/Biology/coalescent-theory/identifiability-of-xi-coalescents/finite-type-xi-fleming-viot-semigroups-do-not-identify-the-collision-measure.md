# Finite-type Ξ-Fleming–Viot semigroups do not identify the collision measure

**Setting.** For $d \ge 2$ let $\Sigma_d = \{y \in [0,1]^d : \sum_k y_k = 1\}$ be the simplex of type frequencies. Let $\mathsf S^\Xi_t$ be the transition semigroup of the neutral $d$-type $\Xi$-Fleming–Viot process without mutation or selection. This is the forward-in-time frequency process dual to the $\Xi$-coalescent with collision measure $\Xi$ on the Kingman simplex $\mathcal K$. For $s \in (0, 1]$, consider the fixed-total-mass slice of $(d+1)$-atom mass partitions
$$\mathcal F^\circ_{d+1,s} = \Big\{p \in \mathcal K : p_1 > \dots > p_{d+1} > 0,\ p_j = 0\ (j > d+1),\ \sum_{i=1}^{d+1} p_i = s\Big\}.$$

**Proposition (finite-support obstruction).** Fix $d \ge 2$, $s \in (0,1]$, a nonempty relatively open $U \subset \mathcal F^\circ_{d+1,s}$ and $\delta > 0$. There are distinct laws $H_{d,s,+} \ne H_{d,s,-}$, compactly supported in $U$ with $C^\infty_c$ densities in the slice's affine coordinates and $0 < \|H_{d,s,+} - H_{d,s,-}\|_{\mathrm{TV}} < \delta$. They satisfy $\mathcal L\big(\sum_j P_jX_j\big) = \mathcal L\big(\sum_j P'_jX'_j\big)$ for $P \sim H_{d,s,+}$, $P' \sim H_{d,s,-}$ and every real i.i.d. mark distribution supported on at most $d$ points.

**Theorem.** For every $d \ge 2$ and $\rho \in (0, 1]$ there are distinct probability collision measures $\Xi_{d,\rho,+} \ne \Xi_{d,\rho,-}$, supported on $\mathcal F^\circ_{d+1,\rho}$, with
$$\mathsf S^{\Xi_{d,\rho,+}}_t f(y) = \mathsf S^{\Xi_{d,\rho,-}}_t f(y) \qquad \text{for all } t \ge 0,\ y \in \Sigma_d,\ f \in C(\Sigma_d).$$
So even the complete mutation-free neutral dynamics of a fixed finite number of types can fail to determine the collision measure. By contrast, the law of one suitably marked sum of block frequencies at a single time does determine it.

## Depends on

- [One-time recovery of a Ξ-coalescent collision measure](one-time-recovery-of-a-xi-coalescent-collision-measure.md)
- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

A mark with at most $d$ values forces two of the $d+1$ masses to receive equal marks, so the marked sum only sees symmetric functions of the masses that a Vandermonde-type polynomial in the $d+1$ coordinates annihilates. A projection obstruction (Cuesta-Albertos, Fraiman and Ransford) plus a differential-operator perturbation then gives a smooth localized pair with equal marked-sum laws for every such mark. To pass to Fleming–Viot, tilt both laws by $V_2(p) = \sum_i p_i^2$. Rademacher marks show $\int V_2\,dH_{d,\rho,+} = \int V_2\,dH_{d,\rho,-} = c_{d,\rho} > 0$, so $\Xi_{d,\rho,\pm} = V_2\,H_{d,\rho,\pm}/c_{d,\rho}$ are probability measures. In the $\Xi$-Fleming–Viot jump generator, the factor $V_2$ cancels the denominator, and a jump of a $d$-type population colors the $d+1$ reproducing families with at most $d$ types. Each generator therefore integrates a marked-sum functional of $H_{d,\rho,\pm}$ with at most $d$ mark values, so the two generators coincide, and so do the semigroups.

## Sources

- J. Lenzi, "One marked-sum law determines random mass partitions and $\Xi$-coalescents", arXiv:2609.12790 (2026), Proposition 1.4, Theorem 7.1, <https://doi.org/10.48550/arXiv.2609.12790>.
