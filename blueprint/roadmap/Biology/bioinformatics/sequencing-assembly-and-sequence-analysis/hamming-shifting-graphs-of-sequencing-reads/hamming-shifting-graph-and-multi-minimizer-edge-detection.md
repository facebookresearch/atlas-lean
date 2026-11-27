# Hamming-shifting graph and multi-minimizer edge detection

**Graph.** For a set $R_S=\{r_1,\dots,r_m\}$ of distinct reads, the **mismatching distance** of $r_i,r_j$ is their Hamming distance when they are aligned without shift, and otherwise the number of mismatches in their overlap plus the (nonzero) shift offset. The Hamming-shifting graph $G_{HaS}(d,R_S)$ joins $r_i\ne r_j$ when this distance is at most $d$; nodes are labelled by duplicate counts and edges by the mismatching bases. Allowing only zero shifts gives the Hamming graph. For compression, edges are weighted by $w=3m_b+o_b$ ($m_b$ mismatches in the overlap, $o_b$ offset bases), each read is encoded against its parent in a minimum spanning forest (Kruskal), and only the root reads are stored in full.

**Edge detection by minimizers.** Reads are bucketed by shared $k$-minimizers (and $k$-maximizers) for several values $k_1,\dots,k_n$. Assume every $k$-mer of a read of length $L$ is equally likely to be its smallest $k$-mer. If the best alignment of two reads has $s$ shifted bases and their overlap contains $t_i$ differing $k_i$-mers, they share the same $k_i$-minimizer with probability

$$p(k_i)=\Bigl(\frac{L-k_i+1-(s+t_i)}{L-k_i+1}\Bigr)^2,$$

which decreases with $k_i$. With independent indexing over $n$ minimizers and $k_j=\max_ik_i$,

$$\mathbb P(\text{the pair shares at least one block})=1-\prod_{i=1}^n\bigl(1-p(k_i)\bigr)\ge1-\bigl(1-p(k_j)\bigr)^n ,$$

with equality iff all $p(k_i)$ are equal. For example $n=20$ and $p(k_j)=0.15$ give probability at least $0.961$.

## Expansion

Two reads sharing a minimizer share a common substring of length at least $k$, which anchors a cheap alignment within each bucket, so all-pairs comparison is avoided. The minimizer of each read is one of its $L-k+1$ $k$-mers, of which $L-k+1-(s+t_i)$ also lie unmodified in the other read; under the uniformity hypothesis both reads pick a common one with the stated squared probability. Smaller $k$ leaves fewer $k$-mers destroyed by mismatches, so it detects more pairs, and the product bound follows from independence across rounds. Since reads from deep sequencing are highly redundant, the resulting graph is extremely sparse, and encoding along its spanning forest yields 10–30% smaller files than previous read compressors.

## Sources

- Y. Liu and J. Li, "Hamming-shifting graph of genomic short reads: efficient construction and its application for compression", PLOS Computational Biology 17(7) (2021) e1009229, <https://doi.org/10.1371/journal.pcbi.1009229>, PMCID PMC8321399. Graph definition, Hypothesis 1, Corollary 1 and Proposition 1.
