# Linear-time bidirected de Bruijn graph construction by radix sorting

A **bidirected graph** on vertex set $V$ has edges $(v_i, v_j, o_1, o_2)$ carrying an arrowhead orientation $o_1, o_2 \in \{\triangleleft, \triangleright\}$ at each endpoint; a walk is valid when, at every intermediate vertex, the arrowhead of the incoming edge matches that of the outgoing edge. In the **bidirected de Bruijn graph of order $k$** ($k$ odd) built from reads $R$ over $\Sigma = \{A, C, G, T\}$, each vertex is a pair (canonical $k$-mer, reverse complement), and two vertices are joined by an oriented edge exactly when the corresponding $k$-mers are adjacent, i.e. overlap by $k-1$ characters inside some $(k+1)$-mer of a read or of its reverse complement.

**Theorem.** Let $n$ be the total number of input characters. Enumerating all $(k+1)$-mers of $R \cup \overline{R}$, canonicalizing them and radix-sorting them builds the bidirected de Bruijn graph in $\Theta(n)$ time, provided $k \log|\Sigma| = O(\log N)$ for $N$ reads (Kundeti et al. 2010, Theorem 1). With $p$ processors the construction runs in $O(n/p)$ time with $O(n)$ messages (Theorem 2), and replacing the radix sort by an external $R$-way merge sort gives an out-of-core construction with an optimal

$$\Theta\!\left(\frac{n}{B}\,\frac{\log(n/B)}{\log(M/B)}\right)$$

I/Os for main memory $M$ and block size $B$ (Theorem 3).

## Expansion

With reads of length $r$ there are $(r-k)N$ candidate $(k+1)$-mers. There are $O(n)$ keys of $(k+1)\log_2|\Sigma| = O(\log N)$ bits each. Radix sorting them with digits of $\Theta(\log N)$ bits makes each pass a counting sort into $O(N)$ buckets, costing $O(n+N) = O(n)$ since $N \le n$, and $O(k\log|\Sigma|/\log N) = O(1)$ passes suffice, so sorting takes $\Theta(n)$ (with constant-width digits, as in the source's proof, the cost $\Theta(kn\log|\Sigma|)$ is only $O(n\log N)$); all other steps (deduplication, orientation assignment from canonical forms) are linear scans of the sorted list, so sorting dominates. Because edges are generated only from $(k+1)$-mers actually present in reads, no spurious edges between $k$-mers that never co-occur arise. For compaction of linear chains, each vertex $v$ is split into $v^+$ and $v^-$ and each bidirected edge into a pair of directed edges; two vertices are connected by a valid bidirected path exactly when the corresponding signed copies are connected by a directed path (Lemma 1), so list ranking on the directed graph compacts chains.

## Sources

- V. K. Kundeti, S. Rajasekaran, H. Dinh, M. Vaughn and V. Thapar, *Efficient parallel and out of core algorithms for constructing large bi-directed de Bruijn graphs*, BMC Bioinformatics 11 (2010), 560, Theorems 1–3 and Lemma 1. <https://doi.org/10.1186/1471-2105-11-560> (PMCID: PMC2996408)
