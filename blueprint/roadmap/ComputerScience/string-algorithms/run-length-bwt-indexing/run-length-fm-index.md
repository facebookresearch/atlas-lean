# Run-length FM-index

The *run-length FM-index* of a text $T$ with $r$ BWT runs stores the BWT as the sequence of run letters and run lengths, using $O(r)$ words, together with rank structures over the run heads so that $\mathrm{rank}_c(\mathrm{BWT}, j)$, the number of occurrences of $c$ in $\mathrm{BWT}[1..j]$, is answered by locating the run containing $j$ (a predecessor search over run starts) and adding a partial count. Backward search for a pattern $P$ maintains the interval $[sp, ep]$ of BWT rows whose suffixes start with the current suffix of $P$.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [FM-index backward search](../burrows-wheeler-transform-and-fm-index/backward-search.md)
- [Rank of a letter in a prefix of the last column](../burrows-wheeler-transform-and-fm-index/rank.md)

## Sources

- Veli Mäkinen, Gonzalo Navarro, "Succinct Suffix Arrays Based on Run-Length Encoding", Nordic Journal of Computing 12(1) (2005).
- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
