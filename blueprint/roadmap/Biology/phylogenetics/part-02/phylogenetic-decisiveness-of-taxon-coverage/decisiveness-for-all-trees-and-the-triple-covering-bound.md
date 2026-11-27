# Decisiveness of taxon coverage for all trees and the triple-covering bound

Let $X$ be a set of $n \ge 4$ taxa and let $\mathcal S = \{Y_1, \dots, Y_k\}$ be a **pattern of taxon coverage**: $Y_j \subseteq X$ is the set of taxa with data for locus $j$, $n_j = |Y_j|$. For a phylogenetic $X$-tree $T$ and $Y \subseteq X$, $T|Y$ is the induced subtree on $Y$. A collection of trees **defines** $T$ if $T$ is the only phylogenetic $X$-tree displaying all of them (so $T$ is binary).

- $\mathcal S$ is **decisive for** a binary tree $T$ if $T|Y_1, \dots, T|Y_k$ define $T$.
- $\mathcal S$ is **phylogenetically decisive for all trees** if, for all binary phylogenetic $X$-trees $T, T'$, $T|Y = T'|Y$ for every $Y \in \mathcal S$ implies $T = T'$.

Rooted trees on $n$ taxa are handled as unrooted trees on $n+1$ taxa with a fixed outgroup.

**Necessary condition (triples).** If $\mathcal S$ is decisive for all trees, then every 3-subset of $X$ is contained in some $Y_j$. A sufficient condition is that some reference taxon $x_0$ lies in every $Y_j$ and every 4-subset containing $x_0$ lies in some $Y_j$; the exact criterion (Steel and Sanderson) is that for every partition of $X$ into four blocks some $Y_j$ meets all four blocks.

**Theorem 1 (locus-number lower bound).** If $\mathcal S$ is phylogenetically decisive for all trees, then

$$\sum_{j=1}^{k} \binom{n_j}{3} \;\ge\; \binom{n}{3}.$$

In particular, if every $n_j \le m$, then $k \ge \binom{n}{3} \big/ \binom{m}{3}$, roughly $(n/m)^3$ loci.

**Comparison with a single tree.** If $\mathcal S$ is decisive for a given tree $T$, then counting internal edges gives

$$\sum_{j=1}^{k} (n_j - 3) \;\ge\; n - 3,$$

so with $n_j \le m$ only about $n/m$ loci are needed; for every binary $T$ there are $n-3$ quadruples decisive for $T$, while any family of quadruples decisive for all trees has size cubic in $n$.

## Depends on

- [An unrooted binary tree is determined by its induced quartet trees](../../quartet-support-and-determination-of-trees-by-qu/iso-of-induces-iff.md)

## Expansion

If some triple $\{a, b, c\}$ lies in no $Y_j$, take a tree $T$ containing the pendant subtree $((a,b),c)$ and replace it by $((a,c),b)$ to obtain $T' \ne T$; every induced subtree $T|Y_j$ misses at least one of the three and is unchanged, so decisiveness fails (this is Lemma 6.2.1 of Semple and Steel). Hence the $\sum_j \binom{n_j}{3}$ triples covered by the loci must include all $\binom{n}{3}$ triples, which is Theorem 1. For a single tree the bound comes from the fact that a defining collection must contribute at least $n-3$ internal edges in total, and $T|Y_j$ has at most $n_j - 3$ of them.

## Sources

- M. J. Sanderson, M. M. McMahon, M. Steel, "Phylogenomics with incomplete taxon coverage: the limits to inference", BMC Evolutionary Biology 10:155 (2010), Theorem 1, Inequalities (1)-(3), and the Appendix proof of Theorem 1, <https://doi.org/10.1186/1471-2148-10-155>, PMCID PMC2897806.