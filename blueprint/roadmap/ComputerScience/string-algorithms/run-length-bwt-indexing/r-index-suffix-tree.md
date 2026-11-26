# Fully functional suffix trees in BWT-runs space

Every text $T$ of length $n$ with $r$ BWT runs has a representation of its suffix tree in $O(r \log\frac{n}{r})$ words that supports the standard navigation operations of compressed suffix trees (parent, child, string depth, suffix link, lowest common ancestor and suffix-array access) in $O(\log\frac{n}{r})$ time each.

## Proof sketch

Gagie, Navarro and Prezza show that the differential suffix array $\mathrm{SA}[j] - \mathrm{SA}[j-1]$, the inverse suffix array and the LCP array all have $O(r)$ runs of repeated substrings in the sense of bidirectional copying, so they can be represented by grammar-like structures of size $O(r\log(n/r))$ with $O(\log(n/r))$-time access; suffix tree navigation reduces to these arrays and range-minimum queries over LCP.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [Suffix tree](../../data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Proof depends on

- [The LCP array](../../data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)
- [The r-index locates in BWT-runs bounded space](r-index-locate.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
