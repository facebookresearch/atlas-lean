# Recombination preserves second-locus allele frequencies at multi-allelic loci

Let $\iota$ and $\kappa$ be finite sets of alleles at a first and a second locus, and let $x$ be a real vector indexed by $\iota \times \kappa$. When the entries of $x$ are nonnegative and sum to $1$, $x_{ij}$ is the frequency of the gamete carrying the alleles $i$ and $j$, and suppose that $\sum_{i, j} x_{ij} = 1$; let its marginals $p_i = \sum_{l \in \kappa} x_{il}$ and $q_j = \sum_{k \in \iota} x_{kj}$ and let $r$ be a
real number. Then the recombination map $x \mapsto x'$, $x'_{ij} = (1 - r)\, x_{ij} + r\, p_i\, q_j$, leaves every second-locus marginal unchanged:
$\sum_{k \in \iota} x'_{kj} = q_j$ for every allele $j \in \kappa$. This generalises
[the two-allele statement](allele-freq-snd-recombine.md) to any finite numbers of alleles.
