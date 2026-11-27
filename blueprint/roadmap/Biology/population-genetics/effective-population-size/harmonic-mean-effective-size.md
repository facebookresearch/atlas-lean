# The harmonic-mean effective size

For a haploid Wright–Fisher population of size $M_N(r) = N S_N(r)$ in generation $r$, with $S_N([N\cdot]) \Rightarrow S$ in the Skorokhod space, the genealogy of a sample converges, with time in units of $N$ generations, to [Kingman's coalescent](../../coalescent-theory/partition-valued-kingman-coalescent/partition-rate.md) run on the random clock $G_t = \int_0^t S(s)^{-1}\,ds$, under the conditions of Kaj and Krone (2003), including $G_t < \infty$ for every $t$ and $G_\infty = \infty$ (Kaj and Krone 2003, Theorem 1, with $c_N = 1/M_N(r)$ and $H(x, y) = 1/y$ for the Wright–Fisher model, eq. (6); restated by Sjödin, Kaj, Krone, Lascoux and Nordborg 2005, eqs. (1)–(2) and Appendix, eqs. (A1)–(A3)). When the size fluctuates fast compared with coalescence, the clock averages: for sizes $N_i = x_iN$ taken independently with probabilities $p_i$ in each generation, the probability that a pair of lineages does not coalesce in $[Nt]$ generations tends to $\exp(-t\sum_ip_i/x_i)$, so the coalescent effective size is the harmonic mean $N_e = (\sum_ip_i/N_i)^{-1}$, and the same holds for a Markov size chain with its stationary law and for jumps at rates $q_{ij}/N^\alpha$ with $0 \le \alpha < 1$; when the fluctuations occur on the coalescent time scale there is no effective size (Sjödin et al. 2005, sections "Fluctuating population size" and Discussion).

The deterministic counterpart is a clock identity. For a neutral Wright–Fisher population whose size is $\nu(t)$ times a reference size, with $\nu$ continuous and positive, the diffusion is the reference-size diffusion $Y$ run on the clock $A(t) = \int_0^t\nu(s)^{-1}ds$, $X_t = Y_{A(t)}$. If $\nu$ is periodic with period $T_0$, then $A(kT_0) = kT_0/\nu_H$ for every integer $k \ge 0$, where $\nu_H = T_0/\int_0^{T_0}\nu(s)^{-1}ds$ is the harmonic mean of $\nu$ over a period: at the ends of whole cycles the clock is that of a constant relative size $\nu_H$. This is the diffusion form of the harmonic-mean effective size of Wright (1938). Over $n$ generations of sizes $N_1, \dots, N_n$ the harmonic mean $n/\sum_i N_i^{-1}$ is at most the arithmetic mean and at most $n \min_i N_i$, so it is governed by the smallest sizes.

## Depends on

- [Rate matrix of Kingman's partition-valued coalescent](../../coalescent-theory/partition-valued-kingman-coalescent/partition-rate.md)
- [Effective population size under fluctuating population size](../../../Biology/population-genetics/effective-population-size/effective-size-under-fluctuating-population-size.md)
- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/time-changed-neutral-diffusion-under-determinist.md)
- [Decay of heterozygosity under a changing population size](../../../Biology/population-genetics/effective-population-size/decay-of-heterozygosity-in-the-time-changed-diffusion.md)

## Expansion

1. The Kaj–Krone time change for the Wright–Fisher model and the averaging of fast fluctuations to the harmonic mean (Sjödin et al. 2005).
2. The clock at cycle ends, $A(kT_0) = kT_0/\nu_H$, for periodic $\nu$.
3. Separate target: the cycle-end equality in law of $(X_{kT_0})_{k \ge 0}$ and $(Y_{kT_0/\nu_H})_{k \ge 0}$ for every period, from $X = Y \circ A$ and item 2, with the statistics it preserves (laws at cycle ends, long-run decay rates of heterozygosity) and those it does not preserve in general (timing within a cycle, or a history that is not repeated, such as a single recent bottleneck).
4. The comparison with the discrete-generation harmonic mean $n/\sum_i N_i^{-1}$.

## Sources

- S. Wright, Size of population and breeding structure in relation to evolution, Science 87 (1938), 430–431.
- I. Kaj and S. M. Krone, The coalescent process in a population with stochastically varying size, J. Appl. Probab. 40(1) (2003), 33–48, Theorem 1 and eq. (6) (Kingman's coalescent run on a time change given by an additive functional of the size process; numbering as in the authors' preprint of July 2002, <https://www2.math.uu.se/~ingekaj/preprints/stochsize.pdf>).
- P. Sjödin, I. Kaj, S. Krone, M. Lascoux and M. Nordborg, On the meaning and existence of an effective population size, Genetics 169 (2005), 1061–1070, section "Fluctuating population size" (fast fluctuations and the harmonic mean; intermediate fluctuations, eqs. (1)–(2)), Appendix, eqs. (A1)–(A3), and Discussion. <https://pmc.ncbi.nlm.nih.gov/articles/PMC1449138/>. <https://doi.org/10.1534/genetics.104.026799>
