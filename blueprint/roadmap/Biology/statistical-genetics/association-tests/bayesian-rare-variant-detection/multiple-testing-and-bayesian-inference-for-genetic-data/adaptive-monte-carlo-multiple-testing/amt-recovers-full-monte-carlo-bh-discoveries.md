# Adaptive Monte Carlo multiple testing recovers the full Monte Carlo Benjamini–Hochberg discoveries

**Setting.** Consider $m$ hypotheses (in a genome-wide association study, one per SNP) with ideal permutation p-values $P_1^{\infty},\dots,P_m^{\infty}$. For hypothesis $i$, Monte Carlo (MC) samples are available of the form

$$
B_{i,1},\dots,B_{i,n}\ \big|\ P_i^{\infty}=p_i^{\infty}\ \overset{\text{i.i.d.}}{\sim}\ \mathrm{Bern}(p_i^{\infty}),
$$

with $B_{i,j}=\mathbf{1}\{T^{\mathrm{null}}_{i,j}\ge T^{\mathrm{obs}}_i\}$ for a permutation null statistic. The *full MC* (fMC) p-values are

$$
P_i^{\mathrm{fMC}}=\frac{1}{n+1}\Big(1+\sum_{j=1}^n B_{i,j}\Big),\qquad i\in[m],
$$

which are conservative under the null. Applying Benjamini–Hochberg (BH) at nominal level $\alpha$ gives the critical rank $r^*=\max\{r\in[m]: P^{\mathrm{fMC}}_{(r)}\le r\alpha/m\}$, the threshold $\tau^*=r^*\alpha/m$, and the discovery set $\mathcal{R}^{\mathrm{fMC}}=\{i: P_i^{\mathrm{fMC}}\le\tau^*\}$. Computing it costs $nm$ samples.

**The AMT algorithm.** Adaptive MC multiple testing (AMT) draws the MC samples of each hypothesis uniformly without replacement from its $n$ fMC samples, in geometric batches $h_l=\gamma^l$ ($\gamma>1$, $L=\Theta(\log n)$ batches), and keeps $\delta/(2mL)$-confidence bounds $p_i^{\mathrm{lb}}\le p_i^{\mathrm{ub}}$ for each $P_i^{\mathrm{fMC}}$. Starting from $\hat r=m$, it repeatedly samples the uncertain hypotheses, then lowers $\hat r$ until

$$
\mathcal{C}_{\mathrm g}=\{i: p_i^{\mathrm{lb}}>\hat r\alpha/m\},\qquad \hat r=m-|\mathcal{C}_{\mathrm g}|,
$$

sets $\hat\tau=\hat r\alpha/m$, $\mathcal U=\{i:p_i^{\mathrm{lb}}\le\hat\tau<p_i^{\mathrm{ub}}\}$ and $\mathcal C_{\mathrm l}=\{i:p_i^{\mathrm{ub}}\le\hat\tau\}$, and stops when $\mathcal U=\emptyset$, returning $\mathcal R^{\mathrm{AMT}}=\mathcal C_{\mathrm l}$.

**Theorem (correctness).** For any failure probability $\delta>0$,

$$
\mathbb P\big(\mathcal R^{\mathrm{AMT}}=\mathcal R^{\mathrm{fMC}}\big)\ \ge\ 1-\delta ,
$$

and this holds even conditionally on any realized set of fMC p-values $\{P_i^{\mathrm{fMC}}\}=\{p_i\}$. Moreover AMT controls the false discovery rate at level $\pi_0\alpha+\delta$, where $\pi_0$ is the proportion of true nulls.

## Depends on

- [Benjamini–Hochberg rejection set](../../../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Proof depends on

- [Benjamini–Hochberg FDR control for super-uniform nulls](../../../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/integral-false-discovery-proportion-bh-r-2.md)

## Expansion

Each hypothesis is an arm of a multi-armed bandit whose mean is its fMC p-value; only arms whose confidence interval straddles the current BH threshold estimate are sampled. Because the bounds are finite-population bounds for sampling without replacement, a hypothesis that receives all $n$ samples has zero uncertainty, so the algorithm always terminates. A union bound over the $m$ hypotheses and $L$ batches shows that, with probability at least $1-\delta$, every confidence interval contains its fMC p-value throughout; on that event the top-down estimate $\hat r$ never passes below $r^*$ and stops exactly at $r^*$, so the output equals $\mathcal R^{\mathrm{fMC}}$. The FDR bound follows because fMC-BH controls FDR at $\pi_0\alpha$ and AMT differs from it with probability at most $\delta$. In practice $\delta=1/m$ makes $\pi_0\alpha+\delta\le\alpha$.

## Sources

- Martin J. Zhang, James Zou, David Tse. *Adaptive Monte Carlo Multiple Testing via Multi-Armed Bandits*, Proceedings of the 36th International Conference on Machine Learning, PMLR 97 (2019), 7512–7522, <https://proceedings.mlr.press/v97/zhang19t.html>; preprint arXiv:1902.00197, <https://doi.org/10.48550/arXiv.1902.00197>: Section 2 (problem formulation), Algorithm 1, Theorems 1–3, Proposition 1 and Remarks 1–2.
