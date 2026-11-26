# Breakpoint median and halving by maximum-weight perfect matching

**Setting.** A gene $g$ has two extremities, a tail $g^t$ and a head $g^h$. A genome $\Pi$ on a gene set of size $n$ is a set of adjacencies (unordered pairs of extremities) in which every extremity lies in at most one adjacency; an extremity in no adjacency is a telomere. Linear and circular chromosomes may both occur (a *mixed* multichromosomal genome). For genomes $\Pi,\Gamma$ on the same genes let $a(\Pi,\Gamma)$ be the number of common adjacencies and $e(\Pi,\Gamma)$ the number of common telomeres. The multichromosomal breakpoint distance is

$$d_{BP}(\Pi,\Gamma) = n - a(\Pi,\Gamma) - \tfrac12\, e(\Pi,\Gamma).$$

For an all-duplicates genome $\Delta$ (two copies $x_1,x_2$ of every extremity) and an ordinary genome $\Pi$, the double distance is $d_{BP}(\Delta,\Pi) = \min d_{BP}(\Delta,\Pi\oplus\Pi)$ over doubled genomes $\Pi\oplus\Pi$; it equals $2n - a(\Pi,\Delta) - \tfrac12 e(\Pi,\Delta)$, where $a(\Pi,\Delta)$ counts, over adjacencies $xy$ of $\Pi$, the adjacencies among $x_1y_1,x_1y_2,x_2y_1,x_2y_2$ in $\Delta$, and $e(\Pi,\Delta)$ counts, over telomeres $x$ of $\Pi$, the telomeres among $x_1,x_2$ in $\Delta$.

**Theorem.** For mixed (and for circular) multichromosomal genomes:
1. **Median.** Given $\Pi_1,\Pi_2,\Pi_3$, a genome $M$ minimizing $s(M) = \sum_{i=1}^3 d_{BP}(\Pi_i,M)$ can be found in polynomial time.
2. **Halving.** Given $\Delta$, a genome $M$ minimizing $d_{BP}(\Delta,M)$ can be found in polynomial time.
3. **Guided halving.** Given $\Delta$ and an ordinary genome $\Pi$, a genome $M$ minimizing $d_{BP}(\Delta,M) + d_{BP}(M,\Pi)$ can be found in polynomial time.

**Construction.** Build a graph $G$ on all $2n$ gene extremities plus one extra vertex $t_x$ per extremity $x$. An edge $xy$ between extremities gets weight equal to the number of input adjacencies supporting it (for the median: genomes $\Pi_i$ containing $xy$; for halving: adjacencies of $\Delta$ among $x_1y_1,\dots,x_2y_2$; for guided halving: both). An edge $x t_x$ gets weight half the number of input telomeres supporting $x$, and every pair $t_x t_y$ is joined by a weight-$0$ edge. A genome $M$ corresponds to the perfect matching using $xy$ and $t_xt_y$ for each adjacency $xy$ of $M$ and $xt_x$ for each telomere $x$, and every perfect matching defines a genome this way. Its weight satisfies

$$w(M) = 3n - s(M)\ \text{(median, guided halving)},\qquad w(M) = 2n - d_{BP}(\Delta,M)\ \text{(halving)},$$

so a maximum-weight perfect matching is an optimal genome.

## Expansion

Each common adjacency between $M$ and an input contributes $1$ and each common telomere contributes $\tfrac12$ to the matching weight, which is exactly the quantity subtracted from $n$ in the breakpoint distance; summing over inputs gives the identities above. Maximum-weight perfect matching is polynomial, so all three problems are. Restricting $G$ to gene extremities (dropping the $t_x$ vertices) forces every extremity into an adjacency and hence yields circular solutions. The same construction does not control linearity: a matching may close chromosomes into circles, which is why the linear versions behave differently. The construction extends to the median of any number of genomes.

## Sources

- E. Tannier, C. Zheng, D. Sankoff, "Multichromosomal median and halving problems under different genomic distances", BMC Bioinformatics 10:120 (2009), breakpoint distance definition (Background), Theorem 1 with Claim 1, Claims 2 and 3, <https://doi.org/10.1186/1471-2105-10-120>, PMCID PMC2683817.
