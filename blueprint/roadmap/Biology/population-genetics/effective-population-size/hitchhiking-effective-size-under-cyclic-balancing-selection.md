# Hitchhiking effective size under cyclically fluctuating balancing selection

Let a selected biallelic locus have a periodic allele-frequency trajectory $\pi_0,\dots,\pi_{G-1}$ ($0<\pi_i<1$) of period $G$ generations, with increments

$$\Delta_i=\pi_{(i+1)\bmod G}-\pi_i,\qquad i=0,\dots,G-1,$$

so that $\sum_i\Delta_i=0$. Following Barton's treatment of hitchhiking under fluctuating selection, random associations of a neutral site at recombination probability $r$ with the two alleles inflate offspring-number variance. They reduce the variance effective size to $N_e=N/F$, where in discrete time

$$F=1+\mathbb E\left[\frac1{p_{\tau'}(1-p_{\tau'})}\Big(\sum_{\tau\ge\tau'}(p_{\tau+1}-p_\tau)\,e^{-r(\tau-\tau')}\Big)^2\right].$$

**Cyclic closed form.** For the periodic trajectory the expectation is the average over the phase $i$ of the cycle, and the infinite sums are geometric:

$$F=1+\frac1G\sum_{i=0}^{G-1}\frac{S_i^2}{\pi_i(1-\pi_i)},\qquad S_i=\frac{\sum_{j=0}^{G-1}\Delta_{(i+j)\bmod G}\,e^{-rj}}{1-e^{-rG}}\quad(r>0).$$

**Tight-linkage limit.** As $r\to0$, $S_i\to\bar p-\pi_i$ with $\bar p=\frac1G\sum_i\pi_i$, and

$$F\to\frac{\bar p^{\,2}}{\tilde p_W}+\frac{(1-\bar p)^2}{\tilde p_S},$$

where $\tilde p_W$ and $\tilde p_S$ are the cycle harmonic means of $\pi_i$ and $1-\pi_i$. This equals $N/N_e$ for the structured coalescent with lineages at stationarity across backgrounds, whose pair coalescence rate is $\frac1{2N}\big(\bar p^2/\tilde p_W+(1-\bar p)^2/\tilde p_S\big)$. In symmetric cycles ($\bar p=\frac12$, $\tilde p_W=\tilde p_S=\tilde p$) the limit is $F\to1/(2\tilde p)$, and substituting $\tilde p=1/(2F)$ into the [structured-coalescent coalescence times](../../coalescent-theory/structured-coalescent/structured-coalescent-linked-to-cyclic-balanced-polymorphism.md) extends them to loose linkage. Unlike $\tilde p$, the factor $F$ at $r>0$ depends on the order of frequencies within the cycle and on the cycle length. Since $F>1$ whenever the trajectory is nonconstant, the reduction persists even at $r=\tfrac12$ (unlinked sites). For $n_l$ selected loci, the genome-wide heterozygosity is approximated by inserting the combined reduction of the single-locus factors into $\frac12[1-1/(1+4uT)]$ with $T=2N/F$.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)
- [Structured coalescent at a neutral site linked to a cyclically fluctuating balanced polymorphism](../../coalescent-theory/structured-coalescent/structured-coalescent-linked-to-cyclic-balanced-polymorphism.md)

## Proof depends on

- [The geometric series of a real ratio r with |r| < 1 sums to 1/(1 − r)](../../../Analysis/sequences-and-series/convergence/limits-of-specific-sequences-and-partial-sums/geometric-series-convergence.md)
- [Structured coalescent at a neutral site linked to a cyclically fluctuating balanced polymorphism](../../coalescent-theory/structured-coalescent/structured-coalescent-linked-to-cyclic-balanced-polymorphism.md)

## Expansion

Writing $\tau-\tau'=cG+j$ with $0\le j<G$, periodicity gives $\Delta_{(i+\tau-\tau')\bmod G}=\Delta_{(i+j)\bmod G}$, and $\sum_{c\ge0}e^{-rGc}=1/(1-e^{-rG})$. This proves the closed form for $S_i$. For the limit, expand $e^{-rj}=1-rj+O(r^2)$ and $1-e^{-rG}=rG+O(r^2)$. The zero-order term of the numerator is $\sum_j\Delta_{i+j}=0$, so

$$S_i\to-\frac1G\sum_{j=0}^{G-1}j\,\Delta_{(i+j)\bmod G}=-\frac1G\Big(G\pi_i-\sum_{l}\pi_l\Big)=\bar p-\pi_i$$

by summation by parts. Then $\frac{(\bar p-\pi)^2}{\pi(1-\pi)}=\frac{\bar p^2}{\pi}-2\bar p+\pi+\frac{(1-\bar p)^2}{1-\pi}-2(1-\bar p)+(1-\pi)$. Its cycle average is $\bar p^2/\tilde p_W+(1-\bar p)^2/\tilde p_S-1$, which gives the limit. The structured-coalescent rate follows because at stationarity a lineage sits in background $W$ at time $t$ with probability $\pi_t$. Each term of $F-1$ is a nonnegative square, and it vanishes for all phases only if every $S_i=0$. For $r>0$ that forces all $\Delta_i=0$, because the circulant map $\Delta\mapsto S$ has eigenvalues $\sum_j\omega^je^{-rj}/(1-e^{-rG})\ne0$ for the $G$-th roots of unity $\omega$. The multi-locus approximation treats the selected loci as acting independently. Against simulations it underestimates the loss of diversity but captures how it scales with $s$ and $n_l$.

## Sources

- M. J. Wittmann, S. Mousset and J. Hermisson, "Modeling the genetic footprint of fluctuating balancing selection: from the local to the genomic scale", Genetics (2023), iyad022, <https://doi.org/10.1093/genetics/iyad022>; equation numbers as in the preprint version, <https://doi.org/10.1101/2022.07.15.500223>. Equations (20)-(27) ("Analytic approximation step 2: Hitchhiking"), Appendix 3 (Equations (A9)-(A22), the $r\to0$ limit), and Equation (31) (multiple selected loci).
- N. H. Barton, "Genetic hitchhiking", Philosophical Transactions of the Royal Society B 355 (2000), 1553-1562, <https://doi.org/10.1098/rstb.2000.0716>, Equation (A6) (the continuous-time factor $F$).
