# Stairway plot: composite likelihood of the SFS under epoch-wise sizes

Let $n$ sequences be sampled and assume the population size is constant within each coalescent epoch, taking value $N_k$ while the genealogy has $k$ lineages, $k=2,\dots,n$, with $\theta_k=4N_k\mu$ per base pair. With $t_k\sim\operatorname{Exp}\big(\binom k2/(2N_k)\big)$, $\mathbb E(t_k)=4N_k/(k(k-1))$, the probability that a site is a SNP of derived-allele count $i$ is

$$p_i=\sum_{k=2}^{n-i+1}k\,P(k,i\mid n)\,\frac{\theta_k}{k(k-1)},\qquad P(k,i\mid n)=\frac{\binom{n-i-1}{k-2}}{\binom{n-1}{k-1}},\qquad 1\le i\le n-1,$$

and $p_0=1-\sum_{i=1}^{n-1}p_i$. Treating sites as unlinked, the composite likelihood of the observed counts $\xi_0,\dots,\xi_{n-1}$ of monomorphic and size-$i$ sites is multinomial,

$$L_n=l_n!\prod_{i=0}^{n-1}\frac{p_i^{\xi_i}}{\xi_i!},\qquad l_n=\sum_{i=0}^{n-1}\xi_i,$$

(and a product of such terms over sites with different numbers of called alleles). The **stairway plot** groups $\theta_2,\dots,\theta_n$ into runs of equal value separated by break points, adds break points greedily one at a time, keeping a new one only if $-2\log(L_{d-1}/L_d)\ge3.84$ (a $1$-degree-of-freedom likelihood-ratio test at level $0.05$), and maps the fitted $\theta_k$ to time by

$$T_i=\sum_{k=i}^n\frac{\theta_k}{k(k-1)},\qquad \theta(T)=\theta_{i-1}\ \text{ for } T_i<T\le T_{i-1},$$

with time measured in mutations per base pair (divide by $\mu$ for generations and $\theta$ by $4\mu$ for individuals).

## Remarks

A mutation on a branch subtending $i$ of $n$ leaves arises during epoch $k$ on one of the $k$ branches, and $P(k,i\mid n)$ is the probability under Kingman's coalescent that a given branch in the $k$-lineage epoch has exactly $i$ descendants; multiplying by $\mu\,\mathbb E(t_k)$ and summing over epochs gives $p_i$, linear in the $\theta_k$. Because the size changes only at coalescent events of the sample, the model is nonparametric yet has at most $n-1$ parameters, and the greedy break-point search trades fit against parsimony. Since the SFS of unlinked sites is used, the method needs no phasing or recombination model and scales to hundreds of samples, with best resolution for recent history where many lineages remain.

## Depends on

- [Expected site frequency spectrum under variable population size](variable-sfs.md)

## Sources

- X. Liu, Y.-X. Fu, "Exploring population size changes using SNP frequency spectra", Nat. Genet. 47 (2015), Online Methods ("Composite likelihood of a SFS", "Estimating θs", "Determining the population size at a given time point"), <https://doi.org/10.1038/ng.3254>, PMCID PMC4414822.
