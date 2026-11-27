# Fertility selection at one autosomal locus: multiplicative reduction and departure from Hardy–Weinberg proportions

Consider one autosomal biallelic locus with genotypes $\mathcal G=\{AA,Aa,aa\}$ and allele-$A$ content $q(AA)=1$, $q(Aa)=\tfrac12$, $q(aa)=0$. Let $u$ and $v$ be the genotype distributions of adult males and females. Under random encounter a mating pair $(g_m,g_f)$ forms with probability $u(g_m)v(g_f)$ and has fertility $f(g_m,g_f)\ge0$; assume the mean fertility $\bar f=\sum_{g_m,g_f}u(g_m)v(g_f)f(g_m,g_f)$ is positive. The zygote law of the next generation is the fertility-weighted mixture of Mendelian offspring laws,

$$z(g)=\frac1{\bar f}\sum_{g_m,g_f}u(g_m)\,v(g_f)\,f(g_m,g_f)\,M(g\mid g_m,g_f),$$

where $M(\cdot\mid g_m,g_f)$ is the law of the unordered genotype formed by one gamete drawn from each parent, a parent of genotype $h$ transmitting $A$ with probability $q(h)$.

1. *Multiplicative fertility.* If $f(g_m,g_f)=a(g_m)\,b(g_f)$ with $a,b\ge0$ and $\sum_g u(g)a(g)>0$, $\sum_g v(g)b(g)>0$, then $z$ is the zygote law produced by random union of gametes from males reweighted by the viabilities $a$ and females reweighted by the viabilities $b$: with $p_m=\sum_g u(g)a(g)q(g)/\sum_g u(g)a(g)$ and $p_f=\sum_g v(g)b(g)q(g)/\sum_g v(g)b(g)$,

$$z(AA)=p_mp_f,\qquad z(Aa)=p_m(1-p_f)+(1-p_m)p_f,\qquad z(aa)=(1-p_m)(1-p_f).$$

So multiplicative fertility selection reduces exactly to [sex-differential viability selection](sex-differential-viability-selection-dioecy.md).

2. *A non-multiplicative fertility leaves Hardy–Weinberg proportions.* Take $u=v=(\tfrac14,\tfrac12,\tfrac14)$ on $(AA,Aa,aa)$, $f(AA,aa)=f(aa,AA)=1$ and $f=0$ for every other pair. Then $\bar f=\tfrac18$ and $z=(0,1,0)$. Since Hardy–Weinberg proportions $(p^2,2p(1-p),(1-p)^2)$ have heterozygote frequency at most $\tfrac12$, the zygote law after one generation is not in Hardy–Weinberg proportions for any allele frequency, although both parental laws are.

Whether some fertility matrix admits a trajectory along which mean fertility $\bar f$ decreases is not asserted here.

## Depends on

- [Sex-differential viability selection makes the sexes' allele frequencies differ](sex-differential-viability-selection-dioecy.md)

## Expansion

A full proof page must establish:

- The factorization in part 1: the mixture over pairs with product weights $u(g_m)a(g_m)\,v(g_f)b(g_f)$ factors into the product of the male and female gamete laws.
- The exact rational computation of part 2, and that this $f$ is not of product form ($a(AA)b(aa)=1$ and $a(aa)b(AA)=1$ force $a(AA)b(AA)>0$, while $f(AA,AA)=0$).
- Whether there exist a fertility matrix $f$ and an initial state for which mean fertility $\bar f$ decreases from one generation to the next; if so, an explicit exact rational example.

## Sources

- R. Bürger, *The Mathematical Theory of Selection, Recombination, and Mutation*, Wiley (2000) (fertility selection).
- W. J. Ewens, *Mathematical Population Genetics I. Theoretical Introduction*, 2nd ed., Springer (2004), <https://link.springer.com/book/10.1007/978-0-387-21822-9> (fertility selection).
