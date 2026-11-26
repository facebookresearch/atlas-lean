# Merging multi-string BWTs with LCP computation

**Setting.** For sequences $s_1,\dots,s_k$ (e.g. sequencing reads) terminated by end-markers $\$_1<\dots<\$_k$ smaller than all other symbols, the multi-string BWT $\mathrm{bwt}_{1\cdots k}$ lists each symbol in the lexicographic order of its context (the suffix following it in its own string), and $\mathrm{lcp}_{1\cdots k}[i]$ is the longest common prefix of the contexts of entries $i-1$ and $i$. Given BWTs $\mathrm{bwt}_1,\dots,\mathrm{bwt}_k$ of sub-collections (computed in RAM), their symbols are already sorted by context within each input, so building $\mathrm{bwt}_{1\cdots k}$ amounts to merging them.

**Gap iteration (Property 1).** Iteration $h$ produces an interleaving vector $Z^{(h)}$ containing $|\mathrm{bwt}_j|$ copies of $j$, such that the $i_1$-th occurrence of $j_1$ precedes the $i_2$-th occurrence of $j_2$ iff the length-$h$ context of $\mathrm{bwt}_{j_1}[i_1]$ is lexicographically smaller than that of $\mathrm{bwt}_{j_2}[i_2]$, or they are equal and $j_1<j_2$. $Z^{(h)}$ is obtained from $Z^{(h-1)}$ by one sequential scan that distributes each symbol into the bucket of its character (counting-sort by the next context symbol). A bit array $B$ marks the starts of blocks of entries sharing their length-$h$ context; when all of $B$ is set, $Z^{(h)}$ describes the final merge.

**LCP extraction.** If $B[i]$ is first set during iteration $h$, then $\mathrm{lcp}_{1\cdots k}[i]=h-1$. Recording these pairs per value of $h$ and multiway-merging the resulting sorted files yields the LCP array. Positions in blocks finalized two or more iterations earlier never change again, so such ranges can be skipped.

**Cost.** The number of iterations is $\mathrm{maxlcp}=\max_i\mathrm{lcp}_{1\cdots k}[i]$. Skipping irrelevant ranges, the data read or written is $O(n\cdot\mathrm{avelcp})$ items, and the merging phase performs $O(n\cdot\mathrm{maxlcp})$ sequential I/Os overall, where $n$ is the total length.

## Expansion

Sorting by length-$h$ contexts is obtained from sorting by length-$(h-1)$ contexts the way radix sort extends a sorted prefix: the symbol $c$ preceding a context in the BWT is the first symbol of the next-longer context, so scanning in the current order and appending each entry to bucket $c$ orders entries by $c$ followed by the previous order. A block boundary that appears only at iteration $h$ separates two contexts agreeing on exactly $h-1$ symbols, which is why the iteration index gives the LCP value without any extra string comparisons.

## Sources

- L. Egidi, F. A. Louza, G. Manzini, G. P. Telles, "External memory BWT and LCP computation for sequence collections with applications", Algorithms for Molecular Biology 14:6 (2019), Background (Equations 1–3 and Property 1), section "The eGap algorithm" (Phases 1–3) and its Analysis, <https://doi.org/10.1186/s13015-019-0140-0>, PMCID: PMC6408864.
