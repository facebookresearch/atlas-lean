# Binomial k-mer test for microbial presence above an ANI threshold

**Simple mutation model.** A genome with average nucleotide identity (ANI) $a \in [0, 1]$ to a reference
is obtained by mutating each site of the reference independently with probability $1 - a$. Let $G$ be
a FracMinHash sketch of the reference's $k$-mers. Assume (with $k$ large and the scale factor small)
that each sketched $k$-mer occurs once in the genome, that sketched $k$-mers do not overlap, and that
mutation never creates a sketched $k$-mer. Then each $k$-mer of $G$ survives unmutated independently
with probability $a^k$, and the sketch of the mutated genome is the random set

$$G^{a} = \{ g \in G : \chi_g = 1 \}, \qquad \chi_g \overset{\text{iid}}{\sim} \mathrm{Bernoulli}(a^k).$$

A metagenomic sample is modelled as $S = \bigcup_{i=1}^{N} G_i^{a_i}$, with $a_i = 0$ for organisms
absent from the sample.

**Hypothesis boundary.** For $n$ $k$-mers, ANI threshold $A$ and level $\alpha$, let
$q(n, k, A, \alpha)$ be the largest integer $q$ with

$$\Pr(X \ge q) \ge \alpha, \qquad X \sim \mathrm{Binom}(n, A^k).$$

**Test.** For a single reference ($N = 1$) with $K = |G|$ sketched $k$-mers, $|S| \sim
\mathrm{Binom}(K, a^k)$, and declaring the organism present iff $|S| \ge q(K, k, A, \alpha)$ has
false-negative probability at most $1 - \alpha$ whenever $a \ge A$. Requiring minimum coverage $C$
replaces $K$ by $\lfloor C K \rfloor$. For $N \ge 1$ references, the test is applied separately to each
genome's **exclusive** $k$-mers $\tilde G_i = G_i \setminus \bigcup_{j \neq i} G_j$ and to
$S_i = \tilde G_i \cap S$, so that no shared $k$-mer supports two organisms.

**Power proxy.** Let $1/2 \le \alpha < 1$ and $q(|\tilde G_i|, k, A, \alpha) \ge 1$. The alternative
significance ANI $a_i^{\alpha}$ is the unique solution in $(0, 1)$ of

$$\Pr\bigl(|S_i| \ge q(|\tilde G_i|, k, A, \alpha) \bigm| a_i = a_i^{\alpha}\bigr) = 1 - \alpha ;$$

it satisfies $a_i^{\alpha} \le A$, and an organism with true ANI below $a_i^{\alpha}$ is reported as a
false positive with probability less than $1 - \alpha$.

## Depends on

- [The k-mers of a string](../../de-bruijn-graph-genome-assembly/kmers.md)

## Expansion

Because all sketched $k$-mers have the same survival probability, the number of shared $k$-mers is
a sufficient statistic, and testing $a \ge A$ is testing $a^k \ge A^k$ for a binomial success
probability. The boundary $q$ is the $\alpha$-quantile cut of $\mathrm{Binom}(n, A^k)$, and since the
binomial tail is increasing in the success probability, any organism with $a \ge A$ shares at least
$q$ $k$-mers with probability at least $\alpha$. The test thus controls false negatives, which
distinguishes a low-abundance organism (few $k$-mers because of coverage, handled by $C$) from a
diverged relative of a reference (few $k$-mers because of mutation). Restricting to exclusive
$k$-mers makes the per-organism tests independent at the cost of power, which is why references
related above the ANI threshold are first thinned to an $A$-distinct subcollection; the closer
$a_i^{\alpha}$ is to $A$, the narrower the band of ANIs in which a false positive is likely.

## Sources

- D. Koslicki, S. White, C. Ma, A. Novikov, "YACHT: an ANI-based statistical test to detect
  microbial presence/absence in a metagenomic sample", Bioinformatics 40 (2024) btae047, Section 2,
  Definitions 1-5, Algorithms 1-3 and Eq. (1), <https://doi.org/10.1093/bioinformatics/btae047>
  (PMC10868342).
