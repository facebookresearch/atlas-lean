# Two-locus two-deme migration–selection model

**Genotypes and fitness.** Two diallelic loci, $\mathsf{A}$ (alleles $A_1, A_2$) and $\mathsf{B}$
(alleles $B_1, B_2$), recombine at rate $\rho \ge 0$ in a diploid population divided into two demes
$k \in \{1, 2\}$; write $k^*$ for the other deme. Fitness is additive within and between loci: in
deme $k$ the Malthusian fitnesses are

$$\begin{array}{c|ccc}
 & B_1B_1 & B_1B_2 & B_2B_2 \\ \hline
A_1A_1 & \alpha_k + \beta_k & \alpha_k & \alpha_k - \beta_k \\
A_1A_2 & \beta_k & 0 & -\beta_k \\
A_2A_2 & -\alpha_k + \beta_k & -\alpha_k & -\alpha_k - \beta_k
\end{array}$$

with $\alpha_1 > 0 > \alpha_2$ and $\beta_1 > 0 > \beta_2$, so $A_1$ and $B_1$ are locally adapted to
deme 1 and $A_2$, $B_2$ to deme 2. Deme $k$ receives a fraction of migrants from deme $k^*$ at rate
$m_k \ge 0$.

**Dynamics.** Let $p_k$ and $q_k$ be the frequencies of $A_1$ and $B_1$ in deme $k$, and
$D_k = x_{1,k} - p_k q_k$ the linkage disequilibrium, where $x_{1,k}$ is the frequency of gamete
$A_1B_1$. In continuous time the state $(p_1, p_2, q_1, q_2, D_1, D_2)$ evolves by

$$\dot p_k = \alpha_k p_k (1 - p_k) + \beta_k D_k + m_k (p_{k^*} - p_k),$$

$$\dot q_k = \beta_k q_k (1 - q_k) + \alpha_k D_k + m_k (q_{k^*} - q_k),$$

$$\dot D_k = \bigl[\alpha_k (1 - 2p_k) + \beta_k (1 - 2q_k) - \rho\bigr] D_k
 + m_k \bigl[(D_{k^*} - D_k) + (p_{k^*} - p_k)(q_{k^*} - q_k)\bigr],$$

for $k = 1, 2$, on the set where all four gamete frequencies
$p_k q_k + D_k$, $p_k(1 - q_k) - D_k$, $(1 - p_k) q_k - D_k$, $(1 - p_k)(1 - q_k) + D_k$ are
nonnegative.

## Depends on

- [Linkage disequilibrium of a two-locus gamete law](../../../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md)

## Expansion

Selection acts on each allele frequency directly through the logistic term and indirectly through
the disequilibrium with the other locus ($\beta_k D_k$ in $\dot p_k$). Migration does three things:
it pulls allele frequencies of the two demes together, it averages their disequilibria, and, through
the term $m_k (p_{k^*} - p_k)(q_{k^*} - q_k)$, it creates new disequilibrium whenever the two demes
differ at both loci in the same direction. Recombination at rate $\rho$ decays disequilibrium. With
locally adapted alleles at both loci, migration-generated positive $D_k$ couples the loci so that
each helps maintain the other's polymorphism: tighter linkage increases differentiation between the
demes. Because all parameters are rates, they can be arbitrarily large, and rescaling time removes
one parameter without changing equilibria.

## Sources

- A. Akerman, R. Bürger, "The consequences of gene flow for local adaptation and differentiation: a
  two-locus two-deme model", Journal of Mathematical Biology 68 (2014), Section 2,
  fitness scheme (2.1), assumption (2.3a) and dynamics (2.7),
  <https://doi.org/10.1007/s00285-013-0660-z> (PMC3948587).
