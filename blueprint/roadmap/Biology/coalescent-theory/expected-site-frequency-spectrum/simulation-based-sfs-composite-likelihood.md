# Simulation-based composite likelihood of the site frequency spectrum

Let a sample of $n$ sequences from one population cover $L$ sites, of which $S$ are polymorphic, and let $m_i$ be the number of sites at which the derived allele occurs in exactly $i$ sequences ($i = 1, \dots, n-1$), so $\sum_i m_i = S$. Under a demographic model with parameters $\theta$ and infinite-sites mutation at rate $\mu$ per site, let $t_i$ be the total length of genealogy branches subtending exactly $i$ leaves and $T = \sum_i t_i$ the total tree length. The probability that a polymorphic site falls in class $i$ is

$$p_i = \frac{\mathbb E(t_i \mid \theta)}{\mathbb E(T \mid \theta)},$$

estimated from $Z$ coalescent simulations by $\hat p_i = \sum_{k=1}^Z t_{i,k} \big/ \sum_{k=1}^Z T_k$. Given one genealogy, $e^{-\mu T}$ is the conditional probability that a site carries no mutation; the model-level probability that a site is monomorphic averages it over genealogies,

$$P_0(\theta) = \mathbb E_\theta\bigl[e^{-\mu T}\bigr],$$

estimated from the same simulations by $\hat P_0 = Z^{-1}\sum_{k=1}^Z e^{-\mu T_k}$ (replacing it by $e^{-\mu\,\mathbb E(T \mid \theta)}$ is a further plug-in approximation). With $P_0 = P_0(\theta)$, the composite likelihood of the observed spectrum is

$$CL(\theta) \propto P_0^{\,L - S}\,(1 - P_0)^{S}\prod_{i=1}^{n-1}\hat p_i^{\,m_i}.$$

For two populations with joint spectrum entries $m_{ij}$ and joint class probabilities $\hat p_{ij}$, the same form holds with the product over $(i, j)$. With a known mutation rate $\mu$, including the monomorphic sites adds information on the absolute scale of the model (for example population sizes in generations rather than only their ratios); it does not by itself make arbitrary demographic parameters identifiable.

## Depends on

- [Expected site frequency spectrum](integral-sfs.md)

## Proof depends on

- [Block counts by size weighted by $T_k$ sum to $\sum_k k\,T_k$](sum-sum-count-mul-eq-sum-mul.md)

## Expansion

Marginally over genealogies, each site is monomorphic with probability $P_0(\theta)$, and, to first order in $\mu$, polymorphic in class $i$ with probability $(1 - P_0)p_i$, since the frequency-class branch lengths sum to the total tree length. Treating sites as independent, the counts are multinomial with likelihood $P_0^{L-S}\prod_i[(1 - P_0)p_i]^{m_i} = P_0^{L-S}(1-P_0)^S\prod_i p_i^{m_i}$. Linked sites share genealogies, so treating them as independent makes this a composite likelihood. fastsimcoal2 maximizes it by a conditional-maximization (ECM) scheme with many independent starts, and for more than two populations collapses rare entries of the multidimensional spectrum or multiplies pairwise composite likelihoods. Methods, Equations (1)–(4).

## Sources

- L. Excoffier, I. Dupanloup, E. Huerta-Sánchez, V. C. Sousa, M. Foll, "Robust Demographic Inference from Genomic and SNP Data", PLoS Genetics 9 (2013), e1003905, <https://doi.org/10.1371/journal.pgen.1003905> (PMC3812088).
