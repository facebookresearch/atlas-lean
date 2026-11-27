# Genome-wide variance of IBD sharing for lineal relatives

For $n\ge1$ and chromosome map length $l>0$ (Morgans) define

$$\varphi_n(l)=\frac{2}{l^2}\Big(\frac14\Big)^n\int_0^l\!\!\int_0^x\Big[\big(1+e^{-2(x-y)}\big)^n-1\Big]\,dy\,dx=\frac{1}{2l^2}\Big(\frac14\Big)^n\sum_{r=1}^n\binom nr\frac{2rl-1+e^{-2rl}}{r^2},$$

and $\varphi_0\equiv0$. Then $\varphi_n(l)\to(\tfrac12)^n\big[1-(\tfrac12)^n\big]$ as $l\to0$ and $\varphi_n(l)\to0$ as $l\to\infty$.

Let two individuals be $g\ge1$ generations apart in direct descent, so $k_2=0$, $k_1=(\tfrac12)^{g-1}$ and $R=(\tfrac12)^g$. At loci with recombination fraction $c$,

$$\operatorname{Cov}(\breve k_{1i},\breve k_{1j})=\Big(\tfrac12(1-c)\Big)^{g-1}-\Big(\tfrac14\Big)^{g-1}.$$

Under Haldane's map function, the proportion $\breve k_1$ of a chromosome of length $l$ shared identical by descent, averaged over infinitely many loci, has

$$\operatorname{Var}_{\mathrm{Lin},g}(\breve k_1,l)=\varphi_{g-1}(l),\qquad \operatorname{Var}(\breve R)=\tfrac14\varphi_{g-1}(l),$$

and for a genome of chromosomes of lengths $l_1,\dots,l_K$ with $L=\sum_il_i$,

$$\operatorname{Var}_{\mathrm{Lin},g}(\breve k_1)=\frac{1}{L^2}\sum_{i=1}^Kl_i^2\,\varphi_{g-1}(l_i).$$

## Depends on

- [Single-locus variance of actual relationship](single-locus-variance-of-actual-relationship.md)
- [Haldane's map function](../../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)

## Expansion

Both loci are shared only if neither of the $g-1$ intervening meioses recombines between them and the shared haplotype is transmitted each time, which has probability $(\tfrac12(1-c))^{g-1}$. Haldane's map gives $1-c=\tfrac12(1+e^{-2d})$, so the covariance is $(\tfrac14)^{g-1}[(1+e^{-2d})^{g-1}-1]$, and averaging over all pairs of positions on $[0,l]^2$ yields the double integral. Expanding the binomial and integrating $e^{-2r(x-y)}$ termwise gives the closed form. Covariances between different chromosomes vanish, which gives the weighted genome sum.

## Sources

- W. G. Hill, B. S. Weir, "Variation in actual relationship as a consequence of Mendelian sampling and linkage", Genet. Res. 93 (2011), Section 2(ii), Equations (2)–(5), <https://doi.org/10.1017/S0016672310000480>, PMCID PMC3070763.
