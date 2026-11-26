# Unbiased sample estimators of frequency-weighted haplotype moments

**Poisson identity.** If $M\sim\mathrm{Poisson}(\lambda)$, then for every integer $i\ge0$ and real $a$,

$$\mathbb E\!\left[\frac{M!}{(M-i)!}\,a^{M-i}\right]=\lambda^i e^{-\lambda(1-a)},$$

where $M!/(M-i)!$ is the falling factorial ($0$ when $M<i$).

**Application to two-locus samples.** Let a sample of $n$ genomes have haplotype counts $n_{Ab},n_{aB},n_{AB}$ that, given the population frequencies $f_{Ab},f_{aB},f_{AB}$, are independent Poisson with means $nf_{Ab},nf_{aB},nf_{AB}$. This is the rare-mutation limit of multinomial sampling. Fix $f_0$ with $nf_0>2$ and define

$$M_{i,j,k}=\frac{n_{Ab}!\,(1-\tfrac1{nf_0})^{n_{Ab}-i}}{n^i\,(n_{Ab}-i)!}\cdot\frac{n_{aB}!\,(1-\tfrac1{nf_0})^{n_{aB}-j}}{n^j\,(n_{aB}-j)!}\cdot\frac{n_{AB}!\,(1-\tfrac2{nf_0})^{n_{AB}-k}}{n^k\,(n_{AB}-k)!}.$$

Then, conditionally on the frequencies,

$$\mathbb E\big[M_{i,j,k}\mid f\big]=f_{Ab}^{\,i}f_{aB}^{\,j}f_{AB}^{\,k}\,e^{-(f_A+f_B)/f_0},\qquad f_A=f_{Ab}+f_{AB},\ f_B=f_{aB}+f_{AB},$$

and therefore, averaging also over the evolutionary process,

$$\langle M_{i,j,k}\rangle=\big\langle f_{Ab}^{\,i}f_{aB}^{\,j}f_{AB}^{\,k}\,e^{-(f_A+f_B)/f_0}\big\rangle .$$

Expanding $D^k$ and $f_A(1-f_A)f_B(1-f_B)$ as polynomials in the haplotype frequencies and replacing each monomial by the matching $M_{i,j,k}$ gives unbiased estimators of the numerator and denominator of the [frequency-resolved LD statistic $\sigma_d^k(f_0)$](frequency-weighted-ld-sigma-d-k-rare-mutation-scaling.md). The estimator of the ratio is their ratio, summed over many locus pairs. The plug-in estimator $f_i=n_i/n$ is biased when counts $nf_i$ are of order ten or less, which dominates for small $f_0$ or large $NR$, $Ns$.

## Depends on

- [Frequency-resolved linkage disequilibrium $\sigma_d^k(f_0)$ and its rare-mutation scaling collapse](frequency-weighted-ld-sigma-d-k-rare-mutation-scaling.md)

## Proof depends on

- [Power series of the exponential function](../../../Analysis/special-functions/elementary-transcendental-functions/real-exponential-power-series.md)

## Expansion

The identity follows from the power series:

$$\sum_{m\ge i}\frac{m!}{(m-i)!}a^{m-i}\frac{\lambda^me^{-\lambda}}{m!}=\lambda^ie^{-\lambda}\sum_{l\ge0}\frac{(a\lambda)^l}{l!}=\lambda^ie^{-\lambda(1-a)}.$$

With $\lambda=nf_{Ab}$ and $a=1-1/(nf_0)$ the factor becomes $n^if_{Ab}^ie^{-f_{Ab}/f_0}$, and likewise for $aB$. For $AB$ the choice $a=1-2/(nf_0)$ gives $e^{-2f_{AB}/f_0}$. Independence multiplies the three factors, and $f_{Ab}+f_{aB}+2f_{AB}=f_A+f_B$. Taking the expectation over frequencies (tower property) gives the unconditional identity. The weight $e^{-(f_A+f_B)/f_0}$ is the only one among the paper's choices for which sample moments map onto population moments this simply. The condition $nf_0>2$ only keeps the base $a$ positive; the identity holds for every real $a$. The paper's printed estimator has a typographical $i$ in place of $j$ in the $aB$ exponent, corrected above.

## Sources

- B. H. Good, "Linkage disequilibrium between rare mutations", Genetics 220(4) (2022), iyac004, <https://doi.org/10.1093/genetics/iyac004>, PMCID PMC8982034. Section "Estimating frequency-resolved LD in finite samples", Equations (71)-(77); explicit estimators for the first moments are in its Appendix G.
