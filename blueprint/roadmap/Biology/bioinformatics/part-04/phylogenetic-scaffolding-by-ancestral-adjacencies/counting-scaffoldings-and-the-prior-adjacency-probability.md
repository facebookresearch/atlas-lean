# Counting scaffoldings and the prior adjacency probability

Consider an extant genome assembled into $n$ linear contigs, each with two distinct extremities, and known to have $p$ linear chromosomes, $n \ge p \ge 1$. A **scaffolding** is a set of $n - p$ adjacencies between contig extremities that joins the contigs into exactly $p$ linear chromosomes. Let $f(n, p)$ be the number of scaffoldings (with $f(n, p) = 0$ if $p > n$ or $p = 0$).

**Lemma.** For all $n \ge 1$ and $p \ge 1$,

$$f(n, p) = \frac{n!}{p!}\,2^{\,n-p}\binom{n-1}{p-1}.$$

**Prior adjacency probability.** For extremities $v_1, v_2$ of two different contigs not adjacent in the data and $n > p$, the probability that a uniformly random scaffolding joins them is

$$P(v_1 \sim v_2) = \rho(v_1, v_2)\,\frac{f(n-1, p)}{f(n, p)} = \rho(v_1, v_2)\,\frac{n - p}{2n(n-1)},$$

where $\rho = 4$ if both contigs are single genes, $2$ if exactly one is, and $1$ otherwise; for $n = p$ it is $1$ for adjacencies in the data and $0$ otherwise. The factor $p(S) = \frac{n - p}{2n(n-1)}$ measures the fragmentation of genome $S$.

**Scaffolding by parsimony.** For gene-tree nodes $v_1, v_2$ of the same species, let $c_1(v_1, v_2)$ and $c_0(v_1, v_2)$ be the minimum total cost of adjacency gains ($\mathrm{Gain}$) and breakages ($\mathrm{Br}$) explaining the extant adjacencies below them, given that $v_1 v_2$ is, respectively is not, an adjacency. On extant leaves the costs are set to

$$c_1(v_1, v_2) = -\log_b P(v_1 \sim v_2), \qquad c_0(v_1, v_2) = -\log_b\big(1 - P(v_1 \sim v_2)\big),$$

and the remaining dynamic program over pairs of reconciled gene trees is unchanged, running in $O(g^2 k^2)$ time for $g$ gene trees of size at most $k$. Requiring $c_1 < c_0 + \mathrm{Br}$, so that an adjacency present in the closest ancestor is always proposed, gives $b > \big((1 - p(S))/p(S)\big)^{1/\mathrm{Br}}$.

## Expansion

The count follows by induction on $n$: removing one contig from a scaffolding into $p$ chromosomes either deletes a whole chromosome or splices out a contig from inside one, and summing the resulting terms with the hockey-stick identity $\sum_{i=r}^{n}\binom{i}{r} = \binom{n+1}{r+1}$ closes the recursion. Equivalently, a scaffolding is an ordered arrangement of the $n$ contigs into $p$ unordered nonempty lists ($\frac{n!}{p!}\binom{n-1}{p-1}$, Lah numbers) with an orientation for each of the $n - p$ joins ($2^{n-p}$). Merging two contigs into one reduces the count from $f(n, p)$ to $f(n - 1, p)$, which yields the ratio and its correction $\rho$ for single-gene contigs whose two extremities coincide. When genomes are completely assembled ($n = p$) the costs reduce to the infinite/zero rules of perfect-assembly parsimony; a Boltzmann weighting $e^{-s(h)/kT}$ of all adjacency histories gives supports for each proposed adjacency.

## Sources

- Y. Anselmetti, V. Berry, C. Chauve, A. Chateau, E. Tannier, S. Bérard, "Ancestral gene synteny reconstruction improves extant species scaffolding", BMC Genomics 16 (Suppl 10) (2015) S11, Methods (partition of adjacencies, a priori adjacency probability, Lemma 1 and the dynamic programming scheme), <https://doi.org/10.1186/1471-2164-16-S10-S11>, PMCID PMC4603332.
