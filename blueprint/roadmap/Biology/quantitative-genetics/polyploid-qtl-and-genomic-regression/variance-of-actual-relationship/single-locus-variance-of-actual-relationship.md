# Single-locus variance of actual relationship

For two non-inbred individuals and one locus, let $\breve k_m\in\{0,1\}$ indicate that they share exactly $m\in\{0,1,2\}$ pairs of alleles identical by descent, with expectations $k_m=E(\breve k_m)$ determined by the pedigree. Exactly one indicator equals $1$, so

$$\operatorname{Var}(\breve k_m)=k_m(1-k_m),\qquad \operatorname{Cov}(\breve k_m,\breve k_{m'})=-k_mk_{m'}\quad(m\ne m').$$

The coancestry is $\theta=\tfrac12k_2+\tfrac14k_1$, the relationship is $R=2\theta=k_2+\tfrac12k_1$, and the actual relationship $\breve R=\breve k_2+\tfrac12\breve k_1$ has $E(\breve R)=R$ and

$$\operatorname{Var}(\breve R)=k_2+\tfrac14k_1-R^2 .$$

For example, full sibs ($k_0,k_1,k_2=\tfrac14,\tfrac12,\tfrac14$) have $R=\tfrac12$ and $\operatorname{SD}(\breve R)=\sqrt{1/8}\approx0.354$, parent and offspring ($k_1=1$) have $\operatorname{Var}(\breve R)=0$, and half sibs, grandparent–grandchild and uncle–nephew ($k_1=k_0=\tfrac12$) have $\operatorname{SD}(\breve R)=\tfrac14$. These single-locus values are also the genome-wide values for completely linked loci.

## Depends on

- [Kinship coefficient by Malécot's recursion](../../pedigree-kinship-and-inbreeding/kinship.md)

## Expansion

Since indicators are idempotent, $E(\breve k_m^2)=k_m$; products of distinct indicators vanish, giving the covariances. Then $E(\breve R^2)=E(\breve k_2)+\tfrac14E(\breve k_1)=k_2+\tfrac14k_1$, because the cross term $\breve k_2\breve k_1$ is identically zero. The quantity $\tfrac14k_2+\tfrac1{16}k_1$ is the probability that two pairs of alleles at the locus are both identical by descent.

## Sources

- W. G. Hill, B. S. Weir, "Variation in actual relationship as a consequence of Mendelian sampling and linkage", Genet. Res. 93 (2011), Section 2(i), Equation (1) and Table 1, <https://doi.org/10.1017/S0016672310000480>, PMCID PMC3070763.
