# Block design of a genotype matrix

For natural numbers $N$, $M$, $K$ and $G$, a block design with $N$ individuals and $M$ markers
consists of a [standardized](is-standardized.md) real $N \times M$ genotype matrix $X$, an LD block
$b(j) \in \mathbb{N}$ for every marker $j$ and a cohort $g(i) \in \mathbb{N}$ for every individual
$i$ such that

- every block has at most $K$ markers and every cohort at most $G$ individuals;
- $X_{ij} \neq 0$ only if $g(i) = b(j)$: individual $i$ is in the cohort of the block of marker $j$.

Within a block the LD is arbitrary; markers of different blocks are
[uncorrelated](ld-corr-eq-zero.md).
