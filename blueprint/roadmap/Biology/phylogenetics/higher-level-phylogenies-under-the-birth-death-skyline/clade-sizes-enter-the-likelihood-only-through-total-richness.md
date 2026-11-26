# Clade sizes enter the higher-level phylogeny likelihood only through total richness

**Setting (birth–death–skyline process).** A single lineage starts at stem age $x_0$ before the present. Time before the present is split as $0 = t_0 < t_1 < \dots < t_k < x_0$; on each interval the speciation and extinction rates are constants $\lambda_i > 0$ and $\mu_i \ge 0$, and they may differ arbitrarily between intervals. The process stops at the present, and extinct lineages are pruned to give the reconstructed tree of extant species. A *higher-level phylogeny* with cut time $x_{\mathrm{cut}} \in (0, x_0)$ keeps the reconstructed tree above $x_{\mathrm{cut}}$: the $n$ lineages alive at $x_{\mathrm{cut}}$ that have extant descendants, their resolved topology and branching times $x_1 > \dots > x_{n-1} > x_{\mathrm{cut}}$, and, for each such lineage $i$, only the number $n_i \ge 1$ of extant species descending from it, with $m = \sum_i n_i$ the total species richness.

**Lemma (geometric clade sizes).** For a lineage alive at time $t$ before the present, let $K(t)$ be its number of extant descendants. Then there are $p_0(t), q(t) \in [0,1)$ such that

$$\Pr\big(K(t) = k\big) = \big(1 - p_0(t)\big)\big(1 - q(t)\big)\,q(t)^{k-1}, \qquad k \ge 1,$$

that is, $K(t)$ conditioned on $K(t) \ge 1$ is geometric. For constant rates $\lambda \ne \mu$ on $[0, t]$, with $r = \lambda - \mu$,

$$p_0(t) = \frac{\mu\,(1 - e^{-rt})}{\lambda - \mu e^{-rt}}, \qquad q(t) = \frac{\lambda\,(1 - e^{-rt})}{\lambda - \mu e^{-rt}}.$$

**Proposition.** The probability density of a higher-level phylogeny factorizes as

$$f(\mathcal T \mid \lambda, \mu) = g\big(\text{tree above } x_{\mathrm{cut}} \mid \lambda, \mu\big)\,\prod_{i=1}^{n} \big(1 - q(x_{\mathrm{cut}})\big)\,q(x_{\mathrm{cut}})^{n_i - 1} = g(\cdot)\,\big(1 - q(x_{\mathrm{cut}})\big)^{n}\,q(x_{\mathrm{cut}})^{m - n},$$

where $g$, the density of the resolved part with each of the $n$ lineages surviving to the present, does not involve the $n_i$. Hence, for fixed tree above the cut, the likelihood depends on the clade sizes $(n_1, \dots, n_n)$ only through $m$: it suffices to know the total number of species, and knowing how they are distributed among tips does not improve rate estimates.

## Expansion

The descendants of distinct lineages alive at $x_{\mathrm{cut}}$ evolve independently, so the clade-size probabilities multiply. For a linear birth–death process with piecewise-constant (indeed any time-varying) rates, the probability generating function of the number of descendants of one lineage is a linear fractional transformation, because compositions of linear fractional maps stay linear fractional; this is the classical result of Kendall (1948), and it is equivalent to the geometric law of the lemma. The product over tips then collapses to $(1 - q)^n q^{\sum_i (n_i - 1)}$. The source uses this likelihood to estimate shifts in diversification rate ($\lambda - \mu$) and turnover ($\mu/\lambda$) through time from phylogenies with one representative per genus or family; simulations show reliable recovery of decelerating diversification for cut times up to half the tree age, whereas accelerating scenarios are recoverable essentially only from complete species-level trees, since most of their branching events lie below the cut.

## Sources

- T. Stadler and J. Smrckova, "Estimating shifts in diversification rates based on higher-level phylogenies", *Biology Letters* (2016), Sections 2(a)–(b) and 3(a), Eq. (3.1) and its total-richness form (proofs in the electronic supplementary material). <https://doi.org/10.1098/rsbl.2016.0273> (PMC5095187)
- D. G. Kendall, "On some modes of population growth leading to R. A. Fisher's logarithmic series distribution", *Biometrika* 35 (1948) 6–15. <https://doi.org/10.1093/biomet/35.1-2.6>
