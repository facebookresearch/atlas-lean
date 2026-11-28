# Read graph and minimal path cover of explaining haplotypes

Let $R$ be a set of aligned, error-corrected reads from a population of haplotypes of common length $n$. Two reads overlap if they are aligned to a common position and agree if they coincide on their overlap; a read is redundant if another read covers it completely and agrees with it. The read graph $G_R$ is the directed acyclic graph with a source $s$, a sink $t$, one vertex per irredundant read, an edge $r_1 \to r_2$ whenever $r_1$ starts before $r_2$, they agree on a nonempty overlap, and no other path from $r_1$ to $r_2$ exists, and edges from $s$ to reads starting at position $1$ and from reads ending at position $n$ to $t$. A haplotype is completely consistent with $R$ if it is assembled from overlapping agreeing reads; these are exactly the $s$–$t$ paths of $G_R$.

**Proposition.** The completely consistent haplotypes explain $R$ (every read is a substring of one of them) if and only if every vertex of $G_R$ lies on a directed $s$–$t$ path.

When this holds, a smallest explaining set of consistent haplotypes is a minimum set of $s$–$t$ paths covering all vertices. By Dilworth's theorem every minimum chain cover of the read poset has the same size, namely the largest number of reads no two of which are joined by a path, and a minimum cover is found by maximum bipartite matching in time at most cubic in the number of irredundant reads.

## Proof depends on

- [Dilworth's theorem](../../../../Combinatorics/partially-ordered-sets/dilworth-s-theorem/dilworth-decomposition.md)

## Expansion

An $s$–$t$ path spells a full-length sequence that agrees with every read on it, which is the meaning of complete consistency, and a read lies in some consistent haplotype exactly when its vertex lies on such a path; that proves the proposition. Reachability makes the irredundant reads a partial order, so a path cover is a chain cover, and Dilworth's theorem equates the minimum number of chains with the maximum antichain; the matching reduction splits each read into an out-copy and an in-copy joined according to reachability, and each matched pair merges two chains, so the minimum chain cover has size equal to the number of reads minus the size of a maximum matching. The minimum cover is a lower bound on the number of haplotypes in the population and is not unique, so extending chains to paths in different ways generates a set of candidate haplotypes for frequency estimation. Before building the graph, errors are corrected locally: in each alignment window a column with $x$ deviations from the consensus among $d$ reads is significant when $\Pr(X \ge x) = \sum_{k=x}^{d} \binom{d}{k} \varepsilon^k (1 - \varepsilon)^{d-k}$ falls below a chosen $\alpha$, where $\varepsilon$ is the per-base error rate.

## Sources

- Eriksson N, Pachter L, Mitsuya Y, Rhee SY, Wang C, Gharizadeh B, Ronaghi M, Shafer RW, Beerenwinkel N. Viral population estimation using pyrosequencing. *PLoS Computational Biology* 4:e1000074 (2008), Results, "Error correction", "Haplotype reconstruction" and "Haplotype frequency estimation", and Methods, "Statistical tests for error correction", equation (1). DOI <https://doi.org/10.1371/journal.pcbi.1000074>. PMCID PMC2323617.
