# Infinite-sites limit of divergence-time uncertainty

**Setting.** Consider Bayesian divergence-time estimation on a fixed rooted tree with node ages $t_1, \dots, t_m > 0$ and a prior on ages built from fossil calibrations. Suppose a strict clock with unknown rate $r$ and an infinitely long alignment, so that the branch lengths in substitutions, $d_b = r\,\Delta t_b$, are known exactly.

**Proposition (strict clock).** In this limit the posterior of the ages is concentrated on the one-dimensional ray $t = T\,c$, where $c = (c_1, \dots, c_m)$ with $c_v > 0$ is fixed by the known branch lengths and $T > 0$ is a single random scale. Consequently, for every node $v$, the posterior mean is $\mathbb{E}[t_v] = c_v \mathbb{E}[T]$ and the width of the equal-tailed $95\%$ credible interval is $w_v = c_v\,(T_{0.975} - T_{0.025})$, so

$$w_v = \kappa\, \mathbb{E}[t_v], \qquad \kappa = \frac{T_{0.975} - T_{0.025}}{\mathbb{E}[T]},$$

for all nodes: in an *infinite-sites plot* of credible-interval width against posterior mean, the points lie on a straight line through the origin whose slope $\kappa$ is set by the fossil calibrations alone. Unlike ordinary estimation, the posterior variance does not tend to $0$ as the amount of sequence data grows.

## Expansion

Known branch lengths fix every ratio $\Delta t_b/\Delta t_{b'} = d_b/d_{b'}$, hence every ratio $t_v/t_{v'}$ of node ages, so all ages are determined by one of them, say $T = t_{\mathrm{root}}$, with $c_v = t_v/t_{\mathrm{root}}$. The posterior of $T$ is the calibration-based time prior restricted to the ray, reweighted by the rate prior evaluated at $r = d_b/\Delta t_b$, and quantiles and means of $c_v T$ scale by $c_v$, which gives the linear law. With relaxed clocks the limit is approached rather than exact, because rates still vary across branches, and points falling on a line indicate that sequence data have been exhausted. In the source, eight primate nodes constrained by a 3.4-million-site alignment lie almost on a line ($R = 0.992$) with fitted slope $0.128$ (each 1 My of divergence adds 0.128 My of interval width), while all 371 nodes of the 372-species tree give a much less linear pattern with slope $0.277$.

## Sources

- M. dos Reis, G. F. Gunnell, J. Barba-Montoya, A. Wilkins, Z. Yang and A. D. Yoder, *Using phylogenomic data to explore the effects of relaxed clocks and calibration strategies on divergence time estimation: primates as a test case*, Systematic Biology (2018). <https://doi.org/10.1093/sysbio/syy001> (PMCID: PMC6005039). Methods: "Rate Prior", "MCMC and Bayesian Selection of Clock Model", "Effect of Genome-Scale Data"; Results: "Effect of Genome-Scale Data" (Figure 6); Discussion: "Clock Model".
- Z. Yang and B. Rannala, *Bayesian estimation of species divergence times under a molecular clock using multiple fossil calibrations with soft bounds*, Molecular Biology and Evolution (2006).
