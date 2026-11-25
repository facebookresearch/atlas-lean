# Pairwise hybrid incompatibility: quadratic expected count and a fitness comparison

Fix integers $K_1,K_2\ge0$ and $p\in[0,1]$. Two parental lineages have fixed
derived alleles at disjoint sets of $K_1$ and $K_2$ loci. Each lineage is
compatible with its own background. For each of the $K_1K_2$ cross-lineage
pairs let $B_{ab}$ be an independent Bernoulli($p$) indicator that the pair is
incompatible. All these derived alleles occur together in an F1 hybrid, and
assume an incompatibility is fully expressed whenever both derived alleles
are present, irrespective of zygosity. Define

$$I=\sum_{a=1}^{K_1}\sum_{b=1}^{K_2}B_{ab},\qquad
 W_{\rm hybrid}=\mathbf 1_{\{I=0\}}.$$

In this idealized lethal-incompatibility model both parental viabilities are
one, while

$$\mathbb E I=pK_1K_2,\qquad
 \mathbb E W_{\rm hybrid}=(1-p)^{K_1K_2}\le1.$$

The empty-pair case has viability one, including $p=1$ and $K_1K_2=0$.
The hybrid comparison is strict if $p>0$ and $K_1K_2>0$.
The first equality uses linearity of expectation; independence is needed
for the displayed viability probability, not for the expected count.

To give an exact continuous-time growth statement, let the numbers of
substitutions in the two lineages be independent Poisson processes of the
same rate $k\ge0$, independent of the incompatibility marks. Conditional on
the counts, use the model above. Then for every $t\ge0$,

$$\mathbb E I(t)=p\,\mathbb E[K_1(t)K_2(t)]=pk^2t^2.$$

This is strictly quadratic growth when $p,k>0$; for $p=0$ or $k=0$ it is
zero. Random counts are not identified with the noninteger real number $kt$.

## Expansion

The fitness comparison is between the parental generation and the specified
F1 cross. Recessive interactions, segregation in F2, local maladaptation,
and nonlethal effects require different explicit fitness models. Orr's
model also discusses ancestral alleles, asymmetry and higher-order
incompatibilities; those claims are not inferred from this simplified
cross-pair calculation. In particular no universal claim that crossing is
harmful, or that reciprocal crosses are asymmetric, follows here.

## Sources

- H. A. Orr, "The population genetics of speciation: the evolution of hybrid incompatibilities", Genetics 139 (1995), 1805–1813, <https://doi.org/10.1093/genetics/139.4.1805>, abstract (motivation from complementary genes and faster-than-linear accumulation). The count, Poisson model and F1 viability comparison above are derived here, not attributed to the abstract as its exact model.
