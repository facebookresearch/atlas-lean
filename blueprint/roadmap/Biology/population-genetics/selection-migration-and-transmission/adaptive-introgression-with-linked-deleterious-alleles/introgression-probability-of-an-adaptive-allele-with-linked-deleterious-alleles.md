# Introgression probability of an adaptive allele with linked deleterious alleles

**Model.** A single hybridization event introduces into a large haploid Moran population (size $N$)
one individual carrying a beneficial allele together with $I$ and $J$ linked deleterious alleles to
its left and right and $F$ unlinked deleterious alleles. While introgressed haplotypes are rare, they
reproduce and recombine only with wild-type individuals, so the early spread is a reducible
multitype branching process: recombination can remove deleterious alleles but never add them.

A carrier of the beneficial allele of type $(i, j; f)$ has net selection coefficient
$\sigma(i, j; f)$: it gives birth at rate $1$ and dies at rate $1 - \sigma(i, j; f)$. At a birth,
each unlinked deleterious allele is transmitted independently with probability $1/2$, and a single
crossover among the linked loci occurs with total probability $r(i, j)$; it produces a type $(i, k)$
offspring with $k < j$ with probability $r^{(i,j)}_{(i,k)}$, or a type $(k, j)$ offspring with
$k < i$ with probability $r^{(i,j)}_{(k,j)}$.

**Theorem.** Let $Q(i, j; f)$ be the extinction probability of the process started by one individual
of type $(i, j; f)$. Writing $\sigma = \sigma(i, j; f)$, $r = r(i, j)$ and $\pi_{f,g} =
\binom{f}{g} 2^{-f}$, these probabilities solve, recursively in $(i, j, f)$ starting from fewer
deleterious alleles,

$$Q(i,j;f) = \frac{1 - \sigma}{2 - \sigma}
 + \frac{Q(i,j;f)}{2 - \sigma} \sum_{g=0}^{f} \pi_{f,g}\Bigl[(1 - r)\, Q(i,j;g)
 + \sum_{k=0}^{i-1} r^{(i,j)}_{(k,j)} Q(k,j;g) + \sum_{k=0}^{j-1} r^{(i,j)}_{(i,k)} Q(i,k;g)\Bigr],$$

a quadratic equation in $Q(i, j; f)$ of which the smaller root is taken. The introgression
probability of the beneficial allele is approximately $1 - Q(I, J; F)$. With no unlinked load
($F = 0$) this reads

$$0 = (1 - r) Q(i,j)^2 + Q(i,j)\Bigl[\sum_{k<j} r^{(i,j)}_{(i,k)} Q(i,k) + \sum_{k<i} r^{(i,j)}_{(k,j)} Q(k,j)\Bigr]
 + 1 - \sigma(i,j) - \bigl(2 - \sigma(i,j)\bigr) Q(i,j).$$

## Depends on

- [Haldane's survival probability of a beneficial mutation](../../haldane-s-survival-probability-of-a-beneficial-m/README.md)

## Expansion

The equation is first-step analysis. The founder dies first with probability
$(1 - \sigma)/(2 - \sigma)$; otherwise it reproduces, after which the lineage dies out only if both the
parent (still of type $(i, j; f)$) and the offspring lineages die out, and the offspring type is
distributed by binomial transmission of the unlinked alleles and at most one crossover. Since
offspring types never carry more deleterious alleles than the parent, the system is triangular and
can be solved from $Q(0, 0; 0)$ upward; with no deleterious load at all it reduces to the
single-type birth–death value $Q = 1 - \sigma$. If the linked load is weak relative to recombination,
$\sigma(i, j) - r(i, j) > 0$, the founding haplotype can establish and drag linked deleterious alleles
to fixation; otherwise it is doomed and introgression succeeds only through a recombinant that has
shed part of the load before the founding lineage dies, so tight linkage to deleterious alleles can
strongly reduce the probability of adaptive introgression.

## Sources

- H. Uecker, D. Setter, J. Hermisson, "Adaptive gene introgression after secondary contact", Journal
  of Mathematical Biology 70 (2015) 1523-1580, model (1a)-(1b), Theorem 1 with Eqs. (2)-(5),
  <https://doi.org/10.1007/s00285-014-0802-y> (PMC4426140).
