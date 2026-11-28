# Counting in BWT-runs space

Using $O(r)$ words, the run-length FM-index counts the occurrences of a pattern $P[1..m]$ in $T$ with $m$ backward-search steps, each consisting of two rank queries and one array lookup, i.e. in $O(m \log\log_w(\sigma + n/r))$ time on a word RAM with $w$-bit words.

## Proof sketch

Backward search updates $sp \leftarrow C[c] + \mathrm{rank}_c(\mathrm{BWT}, sp - 1) + 1$ and $ep \leftarrow C[c] + \mathrm{rank}_c(\mathrm{BWT}, ep)$ for $c = P[i]$, $i = m, \dots, 1$, and the final interval length is the number of occurrences. Each rank on the run-length representation is a predecessor query among the $O(r)$ run starts of letter $c$ plus a constant-time correction, and predecessor search over $O(r)$ keys from a universe of size $n$ costs $O(\log\log_w(n/r))$ with $O(r)$-word structures.

## Depends on

- [Run-length FM-index](run-length-fm-index.md)
- [FM-index backward search](../burrows-wheeler-transform-and-fm-index/backward-search.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Predecessor in doubly logarithmic time](../../data-structures/tries-and-integer-dictionaries/van-emde-boas-tree/predecessor-in-doubly-logarithmic-time.md)

## Sources

- Veli Mäkinen, Gonzalo Navarro, "Succinct Suffix Arrays Based on Run-Length Encoding", Nordic Journal of Computing 12(1) (2005).
- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
