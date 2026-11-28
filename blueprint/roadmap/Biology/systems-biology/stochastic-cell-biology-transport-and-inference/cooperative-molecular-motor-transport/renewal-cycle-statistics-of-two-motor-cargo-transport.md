# Run statistics and effective transport of a cargo carried by two nonidentical motors

**Setting.** A cargo is attached to two cooperative but different motors (e.g. kinesin-1 and kinesin-2), each of which binds to and unbinds from a microtubule. In a scale-separated limit (detached motors fastest, then the cargo, then the attached motors) the system coarse-grains to a continuous-time Markov chain on attachment states $\{(1,2),(1),(2),\emptyset\}$ with effective, configuration-averaged switching rates, while the cargo position $M$ drifts and diffuses within each state. Starting from both motors attached, a run consists of $N+1$ *cycles*: excursions from state $(1,2)$ until the next return to $(1,2)$ or the final complete detachment $\emptyset$. Let $(\Delta T^j,\Delta M^j)$ be the i.i.d. durations and cargo displacements of the cycles, $N$ (geometric) the number of completed detachment–reattachment cycles, $T=\sum_{j=1}^{N+1}\Delta T^j$ the run time and $M_\emptyset=\sum_{j=1}^{N+1}\Delta M^j$ the run length.

**Proposition (run time and length).** By Wald's first identity,

$$\mathbb E T=\mathbb E[N+1]\,\mu_{\Delta T},\qquad \mathbb E M_\emptyset=\mathbb E[N+1]\,\mu_{\Delta M}.$$

The source's Proposition 1(2) also gives compound-sum formulas for $\operatorname{Var}T$, $\operatorname{Var}M_\emptyset$ and $\operatorname{Cov}(T,M_\emptyset)$; they need the cycle increments to be independent of the number of cycles, which fails here because $N+1$ is a stopping time for the cycles (Monte Carlo in this chain with nonidentical motors: $\operatorname{Var}T=5.99$ against the formula's $8.22$), so they are not stated.

**Proposition (effective velocity and diffusivity).** For the *ensemble* (pooled-run) statistics,

$$V_{\rm pool}=\frac{\mu_{M_\emptyset}}{\mu_T}=\frac{\mu_{\Delta M}}{\mu_{\Delta T}},\qquad D_{\rm pool}=\frac{V_{\rm pool}^2\sigma^2_T+\sigma^2_{M_\emptyset}-2V_{\rm pool}\sigma_{T,M_\emptyset}}{2\mu_T}=\frac{V_{\rm pool}^2\sigma^2_{\Delta T}+\sigma^2_{\Delta M}-2V_{\rm pool}\sigma_{\Delta T,\Delta M}}{2\mu_{\Delta T}} ,$$

where the pooled statistics are the limits over independent runs $j=1,\dots,S$ of $\sum_jM^{(j)}_\emptyset/\sum_jT^{(j)}$ and $\sum_j(M^{(j)}_\emptyset-V_{\rm pool}T^{(j)})^2/(2\sum_jT^{(j)})$ as $S\to\infty$ (the source's (72)–(73)). The *long-run* velocity and diffusivity censor the runs to those with more than $k$ completed cycles (the source's (74)–(75)):

$$V_{\rm run}=\lim_{k\to\infty}\lim_{S\to\infty}\frac{\sum_{j=1}^SM^{(j)}_\emptyset\mathbf 1_{\{N^{(j)}>k\}}}{\sum_{j=1}^ST^{(j)}\mathbf 1_{\{N^{(j)}>k\}}},\qquad D_{\rm run}=\lim_{k\to\infty}\lim_{S\to\infty}\frac{\sum_{j=1}^S\big(M^{(j)}_\emptyset-V_{\rm run}T^{(j)}\big)^2\mathbf 1_{\{N^{(j)}>k\}}}{2\sum_{j=1}^ST^{(j)}\mathbf 1_{\{N^{(j)}>k\}}}.$$

Let $\mathcal A$ be the event that a cycle ends with a return to the two-motor state $(1,2)$ rather than with complete detachment, and write $\mu_{\Delta T|\mathcal A}$, $\sigma^2_{\Delta T|\mathcal A}$, $\sigma_{\Delta T,\Delta M|\mathcal A}$, … for the moments of a cycle conditioned on $\mathcal A$. Then (the source's Proposition 2(2), (78)–(79))

$$V_{\rm run}=\frac{\mu_{\Delta M|\mathcal A}}{\mu_{\Delta T|\mathcal A}},\qquad D_{\rm run}=\frac{V_{\rm run}^2\sigma^2_{\Delta T|\mathcal A}+\sigma^2_{\Delta M|\mathcal A}-2V_{\rm run}\sigma_{\Delta T,\Delta M|\mathcal A}}{2\mu_{\Delta T|\mathcal A}}.$$

All cycle moments are explicit in the effective nondimensional rates and single-motor velocities.

**Corollary.** For two identical motors $V_{\rm pool}=V_{\rm run}$ and $|D_{\rm pool}-D_{\rm run}|\le 1/(8\mu_{\Delta T})$; for nonidentical motors the two notions of velocity can differ.

## Expansion

The run is a sum of a stopped number of i.i.d. cycle increments, with $N+1$ a stopping time for the cycle filtration, which is exactly the setting of Wald's identities; the second identity gives the pooled diffusivity in terms of cycle moments. The effective diffusivity $D=\lim\operatorname{Var}(M_t-Vt)/(2t)$ of a renewal–reward process equals the variance of the centered cycle reward $\Delta M-V\Delta T$ divided by twice the mean cycle length, which expands to the stated quadratic form. The scale separation allows the attachment rates to be computed by averaging over the quasi-stationary spring extension, so that force-dependent detachment and the different stepping speeds of the two motor types enter only through a few effective parameters.

## Sources

- Joseph J. Klobusicky, John Fricks, Peter R. Kramer, "Effective behavior of cooperative and nonidentical molecular motors", Research in the Mathematical Sciences 7 (2020), 29, <https://doi.org/10.1007/s40687-020-00230-7>. Published version of arXiv:2007.02169, cited next; locators there refer to the arXiv version.
- J. J. Klobusicky, J. Fricks, P. R. Kramer, "Effective behavior of cooperative and nonidentical molecular motors", arXiv:2007.02169 (2020), Section on transport statistics: Proposition 1 (run length and time), Proposition 2 (velocity and diffusivity), Corollary 1 and Proposition 3 (explicit cycle statistics). <https://doi.org/10.48550/arXiv.2007.02169>
