# Random mating with recombination for two multi-allelic loci

Let $\iota$ and $\kappa$ be finite sets of alleles at a first and a second locus, and let $x$ be a real vector indexed by $\iota \times \kappa$. When the entries of $x$ are nonnegative and sum to $1$, $x_{ij}$ is the frequency of the gamete carrying the alleles $i$ and $j$, and let its marginals $p_i = \sum_{l \in \kappa} x_{il}$ and $q_j = \sum_{k \in \iota} x_{kj}$. For a real number $r$, let

$$x'_{ij} = (1 - r)\, x_{ij} + r\, p_i\, q_j .$$

When $x$ is a probability vector and $0 \le r \le 1/2$, $x'$ are the gamete frequencies after one
generation of random mating with recombination fraction $r$: a fraction $1 - r$ of the haplotypes is
copied and a fraction $r$ is formed by independent assortment of the two loci. For $0 \le r \le 1$,
$x'$ is a convex mixture of $x$ and the product of its marginals, so it is a probability vector
whenever $x$ is one; the values $1/2 < r \le 1$ extend the recurrence algebraically and are not
recombination fractions. This generalises [random mating with recombination](recombine.md) from two
alleles at each locus to any finite numbers of alleles.
