# Suffix-tree functionality in LZ77-bounded space

Every text $T$ of length $n$ has a fully functional suffix tree representation in $O(z \log^3 n)$ words supporting most navigation operations in $O(\log n)$ time (child by a letter and level ancestor in $O(\log^2 n)$), and an index of $O(z\log^2 n)$ words that locates the $\mathit{occ}$ occurrences of a pattern of length $m$ in $O((m + \mathit{occ})\log\log n)$ time; thus results proved for BWT-runs bounded indexes automatically apply in LZ77-bounded space.

## Proof sketch

Substitute $r = O(z\log^2 n)$ into the $O(r\log(n/r))$-word suffix tree and the $O(r)$-word r-index, bounding $\log(n/r) \le \log n$ and $\log\log_w(\sigma + n/r) = O(\log\log n)$.

## Depends on

- [Suffix tree](../../data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)
- [Size $z$ of the greedy LZ77 factorization](../string-attractors-and-repetitiveness-measures/lz77-factorization-size.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)

## Proof depends on

- [Resolution of the BWT-runs conjecture](r-bounded-by-z.md)
- [Fully functional suffix trees in BWT-runs space](../run-length-bwt-indexing/r-index-suffix-tree.md)
- [The r-index locates in BWT-runs bounded space](../run-length-bwt-indexing/r-index-locate.md)

## Sources

- Dominik Kempa, Tomasz Kociumaka, "Resolution of the Burrows-Wheeler Transform Conjecture", FOCS (2020); Communications of the ACM 65(6) (2022), arXiv:1910.10631.
- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
