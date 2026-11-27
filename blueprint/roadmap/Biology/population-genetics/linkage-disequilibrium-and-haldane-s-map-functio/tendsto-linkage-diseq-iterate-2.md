# Multi-allelic linkage disequilibria tend to zero

Let $\iota$ and $\kappa$ be finite sets of alleles at a first and a second locus, and let $x$ be a real vector indexed by $\iota \times \kappa$. When the entries of $x$ are nonnegative and sum to $1$, $x_{ij}$ is the frequency of the gamete carrying the alleles $i$ and $j$, and suppose that $\sum_{i, j} x_{ij} = 1$; let its marginals $p_i = \sum_{l \in \kappa} x_{il}$ and $q_j = \sum_{k \in \iota} x_{kj}$ and let
$0 < r \le 1$. Then for all alleles $i \in \iota$ and $j \in \kappa$, the linkage disequilibrium
$D_{ij}$ of the $t$-th iterate of the recombination map $x \mapsto x'$, $x'_{ij} = (1 - r)\, x_{ij} + r\, p_i\, q_j$, tends to $0$ as $t \to \infty$; biological
recombination fractions satisfy $r \le 1/2$. This generalises
[the two-allele statement](tendsto-linkage-diseq-iterate.md) to any finite numbers of alleles.
