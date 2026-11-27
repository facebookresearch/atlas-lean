# Shared and non-shared $F_{ST}$ on a population tree

**Setting.** At a diallelic locus let $p$ be the reference allele frequency in an ancestral Population 0 and $p_k$ its frequency in Population $k$. The populations form a rooted tree with root 0; every non-root node $q$ has a parent $A(q)$ and a branch parameter $\theta_q \in [0,1]$. Assume

$$\mathbb{E}[p_k \mid p_{A}] = p_{A},\qquad \operatorname{Var}[p_k \mid p_{A}] = \theta_k\, p_{A}(1-p_{A}),\qquad \operatorname{Cov}[p_k, p_{k'} \mid p_{M}] = 0 \ (k \ne k'),$$

where $A = A(k)$ and $M = M(kk')$ is the most recent common ancestor of $k$ and $k'$. Let $P(k)$ be the set of branches on the tree path from 0 to $k$, $Q(kk') = P(k)\cap P(k')$ the shared branches and $R(kk') = P(k)\setminus P(k')$ the branches ancestral to $k$ but not to $k'$. For allele indicators $x_k, y_{k'} \in \{0,1\}$ drawn independently given the population frequencies, define

$$F_{ST}^{W}(kk') = \operatorname{Cor}[x_k, y_{k'} \mid p],\qquad F_{ST}^{H}(kk') = 1 - \frac{\mathbb{P}[x_k \ne y_k] + \mathbb{P}[x_{k'} \ne y_{k'}]}{2\,\mathbb{P}[x_k \ne y_{k'}]}\quad (k\ne k'),$$

with $x_k, y_k$ two distinct alleles from Population $k$ and $F_{ST}^{H}(k) = 0$.

**Theorem.** With empty products equal to one,

$$F_{ST}^{W}(kk') = \frac{\operatorname{Var}[p_M \mid p]}{p(1-p)} = 1 - \prod_{q\in Q(kk')}(1-\theta_q),$$

$$F_{ST}^{H}(kk') = \tfrac12\big\{\operatorname{Cor}[x_k,y_k \mid p_M] + \operatorname{Cor}[x_{k'},y_{k'} \mid p_M]\big\} = 1 - \tfrac12\Big\{\prod_{q\in R(kk')}(1-\theta_q) + \prod_{q\in R(k'k)}(1-\theta_q)\Big\}.$$

So $F_{ST}^{W}$ depends only on the shared branches (root to MRCA) and $F_{ST}^{H}$ only on the non-shared branches (MRCA to tips): the two coefficients use disjoint sets of $\theta$'s. Both are symmetric in $k, k'$. In the star-shaped independent-descent model (every population a child of 0), $F_{ST}^{W}(kk') = 0$ for $k \ne k'$, $F_{ST}^{W}(k) = \theta_k$ and $2F_{ST}^{H}(kk') = \theta_k + \theta_{k'}$.

## Depends on

- [Hierarchical F-statistics](../hierarchical-f-statistics.md)

## Expansion

Each branch multiplies the expected heterozygosity by $1-\theta_q$: from the moment assumptions, $\mathbb{E}[p_k(1-p_k)\mid p_A] = (1-\theta_k)\,p_A(1-p_A)$, so iterating along the path gives $\mathbb{E}[p_M(1-p_M)\mid p] = \prod_{q\in P(M)}(1-\theta_q)\,p(1-p)$ and $\operatorname{Var}[p_M\mid p] = p(1-p) - \mathbb{E}[p_M(1-p_M)\mid p]$, with $P(M) = Q(kk')$. Conditional on $p_M$, $p_k$ and $p_{k'}$ are uncorrelated with mean $p_M$, so the between-population mismatch probability is $2\prod_{Q(kk')}(1-\theta_q)\,p(1-p)$, while the within-population one is $2\prod_{P(k)}(1-\theta_q)\,p(1-p)$. Their ratio is $\prod_{R(kk')}(1-\theta_q)$, which gives the formula for $F_{ST}^{H}$. Adding or removing other populations can move the root and change $F_{ST}^{W}$, but not $F_{ST}^{H}$. A diploid individual can be treated as a population of two gametes, so the same formulas give coancestry coefficients for individuals.

## Sources

- Mary-Huard T, Balding D. Fast and accurate joint inference of coancestry parameters for populations and/or individuals. *PLoS Genetics* 19(1):e1010054 (2023), Theorem 1 (Eqs. 12-13), Eqs. 1-4 and 8. <https://doi.org/10.1371/journal.pgen.1010054>. PMCID: PMC9888729.
