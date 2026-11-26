# The BWT-runs conjecture

The *BWT-runs conjecture* asserts that there is a function $f(n) = (\log n)^{O(1)}$ such that $r(T) \le z(T) \cdot f(|T|)$ for every string $T$, i.e. that the run-length BWT is never more than polylogarithmically larger than the LZ77 factorization. Before its resolution, nearly every other dictionary compressor was known to be within a polylogarithmic factor of $z$ or provably much larger, while no nontrivial upper bound on $r$ was known.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [Size $z$ of the greedy LZ77 factorization](../string-attractors-and-repetitiveness-measures/lz77-factorization-size.md)

## Sources

- Dominik Kempa, Tomasz Kociumaka, "Resolution of the Burrows-Wheeler Transform Conjecture", FOCS (2020); Communications of the ACM 65(6) (2022), arXiv:1910.10631.
- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
