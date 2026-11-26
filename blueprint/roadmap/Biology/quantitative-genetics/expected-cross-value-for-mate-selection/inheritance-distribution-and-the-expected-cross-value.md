# Inheritance distribution and the expected cross value

**Genotype matrix.** For an individual $k$ and $N$ biallelic loci, $L^k\in\{0,1\}^{N\times2}$ has $L^k_{i,j}=1$ iff the allele at locus $i$ on the haplotype received from parent $j$ is desirable.

**Inheritance distribution.** A random vector $J\in\{0,1\}^N$ follows $\mathcal I(r,\alpha_0)$, with recombination frequencies $r\in[0,0.5]^{N-1}$ between consecutive loci, if $\Pr(J_1=0)=\alpha_0$ and, for $i\ge2$, $\Pr(J_i=J_{i-1})=1-r_{i-1}$, $\Pr(J_i=1-J_{i-1})=r_{i-1}$. Here $J_i=0$ means locus $i$ of the gamete is copied from the first haplotype (column) and $J_i=1$ from the second. The gamete of an individual with genotype matrix $L$ is $g_i=L_{i,1}(1-J_i)+L_{i,2}J_i$.

**Proposition 1 (marginal transmission).** Define $\phi_1(r)=0$, $\phi_2(r)=r_1$ and $\phi_i(r)=r_{i-1}+(1-2r_{i-1})\phi_{i-1}(r)$ for $i\ge3$. If $J\sim\mathcal I(r,\alpha_0)$ then

$$\Pr(J_i=0)=\alpha_0+(1-2\alpha_0)\phi_i(r),\qquad \Pr(J_i=1)=1-\alpha_0+(2\alpha_0-1)\phi_i(r).$$

**Corollary 1.** Under unbiased segregation ($\alpha_0=1/2$), $\Pr(J_i=0)=\Pr(J_i=1)=\mathbb E J_i=1/2$ for every locus, whatever $r$.

**Expected cross value.** Cross parents $L^1,L^2$ with independent $J^1,J^2,J^3\sim\mathcal I(r,\alpha_0)$: the child is $[g^1,g^2]$ with $g^k=\mathrm{gam}(L^k,J^k)$, and its gamete is $g^3=\mathrm{gam}([g^1,g^2],J^3)$. The ECV is $\mathrm{ECV}(L^1,L^2,r,\alpha_0)=\mathbb E\sum_ig^3_i$, the expected number of desirable alleles in $g^3$ (in contrast to the predicted cross value $\Pr(g^3\equiv1)$).

**Theorem 1.** Writing $q_i=1-\alpha_0+(2\alpha_0-1)\phi_i(r)$,

$$\mathrm{ECV}=\sum_{i=1}^N\Big[L^1_{i,1}+q_i\big(L^1_{i,2}-2L^1_{i,1}+L^2_{i,1}\big)+q_i^2\big(L^2_{i,2}+L^1_{i,1}-L^1_{i,2}-L^2_{i,1}\big)\Big],$$

and under unbiased segregation ($\alpha_0=1/2$)

$$\mathrm{ECV}(L^1,L^2,r,1/2)=\frac14\sum_{i=1}^N\big(L^1_{i,1}+L^1_{i,2}+L^2_{i,1}+L^2_{i,2}\big).$$

## Expansion

$J$ is a two-state Markov chain whose state flips between loci $i-1$ and $i$ with probability $r_{i-1}$, so $\phi_i$ is the probability of an odd number of flips between locus $1$ and locus $i$; the recursion conditions on the last step, and the marginals follow from the initial distribution. Because $g^3_i$ is linear in $J^3_i$ and in the entries of $g^1,g^2$, and the $J^k$ are independent, $\mathbb Eg^3_i=(1-q_i)^2L^1_{i,1}+q_i(1-q_i)(L^1_{i,2}+L^2_{i,1})+q_i^2L^2_{i,2}$, which expands to Theorem 1. With $q_i=1/2$ the four parental alleles each reach the grandchild gamete with probability $1/4$, so linkage drops out of the expectation; it still matters for the probability of an all-desirable gamete. Linearity of the ECV in the binary genotype entries is what makes parental selection, including multi-trait versions with one genotype matrix per trait, an integer linear program.

## Sources

- Ahadi P, Balasundaram B, Borrero JS, Chen C, "Development and optimization of expected cross value for mate selection problems" (2024), Definitions 1-6, Proposition 1, Corollary 1, Theorem 1 and Remark 1, <https://doi.org/10.1038/s41437-024-00697-y>, PMCID PMC11286873.
