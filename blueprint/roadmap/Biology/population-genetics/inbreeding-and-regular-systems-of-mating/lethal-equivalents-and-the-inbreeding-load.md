# Lethal equivalents and the inbreeding load

Consider $L$ loci with multiplicative fitness across loci. At locus $l$ the deleterious allele has frequency $q_l$ ($p_l = 1 - q_l$) and the genotypes have fitnesses $1$, $1 - h_l s_l$, $1 - s_l$ with $0 < s_l \le 1$ and $0 \le h_l \le 1$. An individual with inbreeding coefficient $F \in [0,1]$ has at each locus the genotype frequencies of [an inbred individual](genotype-frequencies-under-inbreeding.md), and assume its genotypes at different loci are independent. Write $\bar w_l(F)$ for the mean fitness at locus $l$ and $W(F) = \prod_l \bar w_l(F)$.

**Proposition.** With $b_l = p_l q_l s_l (1 - 2h_l)/\bar w_l(0)$,

$$\ln W(F) = \ln W(0) + \sum_{l=1}^{L} \ln(1 - F b_l),$$

so when every $F b_l$ is small,

$$\ln W(F) \approx -(A + BF), \qquad A = -\ln W(0), \qquad B = \sum_{l=1}^{L} b_l .$$

Since each $F \mapsto \ln(1 - Fb_l)$ is concave, $\ln W$ is concave in $F$ and the linear form is an upper bound: $\ln W(F) \le \ln W(0) - BF$ for all $F \in [0,1]$. If $h_l \le \tfrac12$ for all $l$, every $b_l \ge 0$ and $\ln W$ decreases with $F$.

The slope $B$ is the **number of lethal equivalents** (per gamete): the total inbreeding load, expressed as the number of recessive lethals that would cause the same decline of log fitness. For rare fully recessive lethals ($s_l = 1$, $h_l = 0$, $q_l \to 0$), $b_l = p_l q_l/(1 - q_l^2) \approx q_l$, so $B$ is the expected number of lethal alleles carried by a gamete. Detrimental alleles of small effect contribute $b_l \approx s_l q_l(1 - 2h_l)$ each, and many of them add up to lethal equivalents. Completely inbred individuals ($F = 1$) have log fitness lower than outbred ones by approximately $B$.

## Proof sketch

By the single-locus result, $\bar w_l(F) = \bar w_l(0) - F p_l q_l s_l(1 - 2h_l) = \bar w_l(0)(1 - F b_l)$. Multiplicativity and independence across loci turn the product of means into a sum of logarithms, and $\ln(1 - x) \le -x$ with near equality for small $x$ gives both the linear approximation and the bound. This is the Morton–Crow–Muller regression of log survival on $F$: $A$ measures the load expressed in the outbred population, $B$ the load concealed in heterozygotes that inbreeding exposes. Because only partially recessive alleles ($h < \tfrac12$) contribute positively, the size of $B$ is evidence about dominance. Selection against homozygotes exposed by inbreeding can remove these alleles (purging), which lowers $B$ over generations of inbreeding; Hedrick and García-Dorado review estimates of lethal equivalents, purging, and genetic rescue in this framework.

## Depends on

- [Genotype frequencies of an inbred individual](genotype-frequencies-under-inbreeding.md)

## Proof depends on

- [Mean fitness is linear in the inbreeding coefficient](mean-fitness-under-inbreeding.md)

## Sources

- N. E. Morton, J. F. Crow and H. J. Muller, "An estimate of the mutational damage in man from data on consanguineous marriages", Proceedings of the National Academy of Sciences USA 42 (1956), 855–863, <https://doi.org/10.1073/pnas.42.11.855>.
- P. W. Hedrick and A. García-Dorado, "Understanding inbreeding depression, purging, and genetic rescue", Trends in Ecology & Evolution 31 (2016), <https://doi.org/10.1016/j.tree.2016.09.005>.
