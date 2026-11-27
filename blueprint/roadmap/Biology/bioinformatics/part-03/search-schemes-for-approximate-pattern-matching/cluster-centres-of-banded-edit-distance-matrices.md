# Cluster centres of banded edit-distance matrices

**Setting.** Let $X$ and $Y$ be strings and $AM$ their edit-distance dynamic-programming matrix, $AM[i,j]$ being the edit distance between the length-$i$ prefix of one string and the length-$j$ prefix of the other. Adjacent cells in a row or column differ by at most $1$.

**Clusters.** In a fixed column $j$, a *cluster* $\{s,c,e\}$ with $s \le c < e$ is the set of cells $AM[i,j]$, $s \le i < e$, such that

$$AM[i,j] = AM[c,j] + |c-i| .$$

The cell $AM[c,j]$ is the cluster's *centre*, a local minimum of the column.

**Lemma 1.** For every optimal alignment path that passes through one or more cells of a cluster $\{s,c,e\}$ but not through its centre, there is an alternative optimal alignment path that passes through the centre.

**Consequence.** When a search scheme extends a partial match from one pattern part to the next in the same direction, partial occurrences ending in non-centre cells of a cluster in the final column of the current banded matrix are redundant and need not be extended separately, which allows the band of the next part to be narrowed.

## Depends on

- [Search schemes and the pigeonhole principle](search-schemes-and-the-pigeonhole-principle.md)
- [Edit distance algorithm](../../../../ComputerScience/string-algorithms/edit-distance/edit-distance.md)

## Expansion

Suppose the optimal path passes through $AM[i,j]$ with $s \le i < c$, so $AM[i,j] = AM[c,j] + (c-i)$, and let $AM[c,k]$ be the leftmost cell of row $c$ on the path. Costs never decrease along an alignment path, so $AM[c,k] \ge AM[i,j] = AM[c,j] + (c-i)$; on the other hand moving along row $c$ from column $j$ to column $k$ costs at most $k-j$, so $AM[c,k] \le AM[c,j] + (k-j)$. Combining the two inequalities gives $k - j \ge c - i$, and rerouting the path through the centre $AM[c,j]$ and then along row $c$ to $AM[c,k]$ costs no more than the original path. The case $c < i < e$ is symmetric. The lemma removes duplicated partial occurrences that differ only by where an indel is placed at a part boundary, a major source of redundancy in edit-distance search.

## Sources

- L. Renders, K. Marchal, J. Fostier, "Dynamic partitioning of search patterns for approximate pattern matching using search schemes", iScience 24(7) (2021) 102687, Lemma 1 and the section on reducing redundancy for the edit distance metric, <https://doi.org/10.1016/j.isci.2021.102687>, PMCID PMC8246400.
