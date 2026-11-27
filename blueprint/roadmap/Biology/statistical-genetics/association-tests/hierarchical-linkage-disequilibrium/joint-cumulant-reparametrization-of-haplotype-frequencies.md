# Joint-cumulant reparametrization of haplotype frequencies

**Setting.** Consider $M$ biallelic loci with alleles coded $A_j\in\{0,1\}$, and a haplotype $h\in H=\{0,1\}^M$ drawn as $h\sim\mathrm{Mult}(1,\theta)$ with $\theta=(\theta_h)_{h\in H}$, $\theta_h\in(0,1)$, $\sum_h\theta_h=1$ ($2^M-1$ free parameters).

**Joint cumulant.** For a set $A=\{A_1,\dots,A_M\}$ of random variables, let $\mathcal P_A$ be the set of partitions of $A$ into nonempty blocks. The joint cumulant is

$$\kappa(A)=\sum_{p\in\mathcal P_A}(-1)^{|p|-1}(|p|-1)!\prod_{b\in p}E\Bigl[\prod_{A_i\in b}A_i\Bigr].$$

For one variable it is the mean and for two it is the covariance.

**Lemma (reparametrization).** For each nonempty subset $s\in S=2^{A}\setminus\{\emptyset\}$ put $\delta_s=\kappa(s)$. Then $\delta=(\delta_s)_{s\in S}$ is a reparametrization of $\theta$.

First-order parameters are allele frequencies $\delta_j=E(A_j)$, second-order parameters are the usual pairwise LD coefficients

$$\delta_{jk}=\eta_{jk}-\delta_j\delta_k,\qquad \eta_{jk}=E(A_jA_k),$$

and the third-order LD parameter is

$$\delta_{123}=\eta_{123}-\delta_1\eta_{23}-\delta_2\eta_{13}-\delta_3\eta_{12}+2\delta_1\delta_2\delta_3 .$$

A cumulant vanishes whenever its loci split into two mutually independent groups.

**Hierarchical estimation.** Writing $\delta_A=\eta_A-R_\delta$, where $\eta_A=E\prod_{A_i\in A}A_i$ and the remainder $R_\delta$ involves only lower-order parameters, each $\delta_s$ can be estimated by a one-dimensional optimization over $\eta_s$ once all lower-order parameters are fixed. Starting from the $M$ allele frequencies, the full fit needs $2^M-1-M$ single-parameter optimizations and no EM algorithm, even with unphased genotypes under Hardy–Weinberg equilibrium.

**Standardized LD of any order.** Holding $R_\delta$ fixed, let $\eta_A^{\max},\eta_A^{\min}$ be the attainable bounds of $\eta_A$. Set $\delta_A^{\max}=\eta_A^{\max}-R_\delta$ if $\delta_A\ge0$ and $\eta_A^{\min}-R_\delta$ if $\delta_A<0$, and $\delta'_A=\delta_A/\delta_A^{\max}$. For two loci this is Lewontin's $D'$; $|\delta'_A|=1$ means at least one haplotype on those loci is absent.

## Depends on

- [Multinomial distribution](../../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Expansion

Haplotype frequencies and the moments $\eta_s$ ($s\subseteq A$) determine each other by inclusion–exclusion over $\{0,1\}^M$, and moments and cumulants determine each other by Möbius inversion on the partition lattice, so $\theta\leftrightarrow\delta$ is a bijection onto its image. Because $\delta_s$ involves $\eta_s$ linearly with coefficient one and otherwise only moments of proper subsets, the parameters can be fitted order by order.

## Sources

- B. Balliu, J. J. Houwing-Duistermaat, S. Böhringer, "Powerful testing via hierarchical linkage disequilibrium in haplotype association studies", *Biometrical Journal* (2019), Lemma 1 and Equations (2)–(3) in "Reparametrization of the multinomial haplotype distribution", sections "Parameter estimation" and "Standardized LD parameters", <https://doi.org/10.1002/bimj.201800053>, PMCID PMC6637384.
