# Optimal reverse-complement-complete sequences

Work over the DNA alphabet $\{A,C,G,T\}$ with complement $A \leftrightarrow T$, $C \leftrightarrow G$; $\mathrm{RC}(s)$ is $s$ reversed and complemented, and $s$ is a *palindrome* if $\mathrm{RC}(s) = s$. Measure the length of a sequence by its number of $k$-mers (a sequence of length $t$ has $t + k - 1$ letters). A sequence $s$ is *RC complete of order $k$* if for every $k$-mer $x$ at least one of $x$, $\mathrm{RC}(x)$ occurs in $s$; it is *optimal* if no RC complete sequence of order $k$ is shorter. Let $L(k)$ be the optimal length.

1. **Lower bound.** For odd $k$ there are no palindromic $k$-mers, and for even $k$ there are exactly $4^{k/2}$. Hence

    $$L(k) \ge \begin{cases} \dfrac{4^k}{2}, & k \text{ odd}, \\[2mm] \dfrac{4^k + 4^{k/2}}{2}, & k \text{ even}. \end{cases}$$

2. **Odd $k$: characterization.** An RC complete sequence $s$ attains the bound if and only if $s$ and $\mathrm{RC}(s)$ correspond to two edge-disjoint paths without repeated edges in the de Bruijn graph of order $k-1$ that together cover all its edges.
3. **Odd $k$: construction.** An Euler-tour traversal that, whenever it appends an edge $e$ to the forward path, prepends $\mathrm{RC}(e)$ to a reverse path and marks both, outputs such a pair. It runs in time linear in the size of the graph, so the bound $4^k/2$ is attained.
4. **Even $k$.** The bound is not tight. Augmenting the graph with paths that connect the palindromic $k$-mers in pairs, chosen by a maximum-weight matching of palindrome overlaps, gives an optimal RC complete sequence in time polynomial in the size of the de Bruijn graph of order $k-1$.

For every $k$ the optimal sequence is roughly half the length $4^k$ of a de Bruijn sequence of order $k$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

For the lower bound, the non-palindromic $k$-mers fall into reverse-complement pairs, at least one member of each pair must occur, and every palindrome must occur; a palindrome of even length is fixed by its first $k/2$ letters. In the de Bruijn graph of order $k-1$ each $k$-mer is an edge, every vertex has in- and out-degree $4$, and the graph is strongly connected. For odd $k$, $e \mapsto \mathrm{RC}(e)$ is a perfect matching of the edges into distinct pairs. An optimal sequence repeats no $k$-mer, so it is a path $F$, and $\mathrm{RC}$ of it is the reversed path $R$ through the complementary edges. Together they use every edge once, each taking exactly half. In the construction, if the forward walk reaches a dead end then so does the reverse one, and both close cycles. The cycles can be spliced as in Hierholzer's algorithm, and strong connectivity forces the forward and reverse cycle sets to cover a single component together. For even $k$ the palindromic edges are self-paired, so extra edges must be added; pairing palindromes along shortest connecting paths, and decomposing matching cycles into cycles through exactly two palindromes, keeps the added edges in reverse-complement pairs without losing optimality.

## Sources

- Y. Orenstein, R. Shamir, "Design of shortest double-stranded DNA sequences covering all k-mers with applications to protein-binding microarrays and synthetic enhancers", *Bioinformatics* (2013), Section 2 (definitions), Section 3.1 (Proposition 1), Section 3.2 (Theorems 1–2, Algorithm 1, Lemmas 1–3) and Section 3.3 (Theorems 3–6, Lemmas 4–6, Proposition 2), <https://doi.org/10.1093/bioinformatics/btt230> (PMC3694677).
