# One generation of recombination multiplies each multi-allelic disequilibrium by $1 - r$

Let $\iota$ and $\kappa$ be finite sets of alleles at a first and a second locus, and let $x$ be a real vector indexed by $\iota \times \kappa$. When the entries of $x$ are nonnegative and sum to $1$, $x_{ij}$ is the frequency of the gamete carrying the alleles $i$ and $j$, and suppose that $\sum_{i, j} x_{ij} = 1$; let its marginals $p_i = \sum_{l \in \kappa} x_{il}$ and $q_j = \sum_{k \in \iota} x_{kj}$ and let $r$ be a
real number. Under the recombination map $x \mapsto x'$, $x'_{ij} = (1 - r)\, x_{ij} + r\, p_i\, q_j$, every pairwise linkage disequilibrium
$D_{ij} = x_{ij} - p_i q_j$ is multiplied by $1 - r$: the disequilibrium $D'_{ij}$ of $x'$ equals
$(1 - r)\, D_{ij}$. This generalises [the two-allele statement](linkage-diseq-recombine.md) to any
finite numbers of alleles.
