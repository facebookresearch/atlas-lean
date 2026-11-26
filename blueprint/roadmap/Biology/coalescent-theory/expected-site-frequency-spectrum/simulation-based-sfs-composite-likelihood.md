# Simulation-based composite likelihood of the site frequency spectrum

Let a sample of $n$ sequences from one population cover $L$ sites, of which $S$ are polymorphic, and let $m_i$ be the number of sites at which the derived allele occurs in exactly $i$ sequences ($i = 1, \dots, n-1$), so $\sum_i m_i = S$. Under a demographic model with parameters $\theta$ and infinite-sites mutation at rate $\mu$ per site, let $t_i$ be the total length of genealogy branches subtending exactly $i$ leaves and $T = \sum_i t_i$ the total tree length. The probability that a polymorphic site falls in class $i$ is
$$p_i = \frac{\mathbb E(t_i \mid \theta)}{\mathbb E(T \mid \theta)},$$
estimated from $Z$ coalescent simulations by $\hat p_i = \sum_{k=1}^Z t_{i,k} \big/ \sum_{k=1}^Z T_k$. With $P_0 = e^{-\mu T}$ the probability of no mutation on the tree at a site, the composite likelihood of the observed spectrum is
$$CL(\theta) \propto P_0^{\,L - S}\,(1 - P_0)^{S}\prod_{i=1}^{n-1}\hat p_i^{\,m_i}.$$
For two populations with joint spectrum entries $m_{ij}$ and joint class probabilities $\hat p_{ij}$, the same form holds with the product over $(i, j)$. Including the monomorphic sites makes absolute parameter values (e.g. population sizes in units of the mutation rate) identifiable, not just ratios.

## Depends on

- [Expected site frequency spectrum](integral-sfs.md)

## Expansion

Each site is independently monomorphic with probability $P_0$ or polymorphic in class $i$ with probability $(1 - P_0)p_i$, so the counts are multinomial with likelihood $P_0^{L-S}\prod_i[(1 - P_0)p_i]^{m_i} = P_0^{L-S}(1-P_0)^S\prod_i p_i^{m_i}$. Treating linked sites as independent makes this a composite likelihood. fastsimcoal2 maximizes it by a conditional-maximization (ECM) scheme with many independent starts, and for more than two populations collapses rare entries of the multidimensional spectrum or multiplies pairwise composite likelihoods. Methods, Equations (1)–(4).

## Sources

- L. Excoffier, I. Dupanloup, E. Huerta-Sánchez, V. C. Sousa, M. Foll, "Robust Demographic Inference from Genomic and SNP Data", PLoS Genetics 9 (2013), e1003905, <https://doi.org/10.1371/journal.pgen.1003905> (PMC3812088).
