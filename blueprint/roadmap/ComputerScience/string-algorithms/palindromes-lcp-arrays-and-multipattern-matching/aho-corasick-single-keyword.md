# Aho-Corasick with one keyword is Knuth-Morris-Pratt

For a single nonempty keyword $p$, the Aho-Corasick failure state of the prefix of length $q$ ($1 \le q \le |p|$) is the prefix of length $\pi_p(q)$ given by the KMP prefix function, and the occurrences reported by Aho-Corasick are exactly the KMP match shifts $s$, each reported at end position $s + |p|$.

## Depends on

- [Aho–Corasick automaton construction and scanning time](../string-matching-specifications/the-ahocorasick-algorithm.md)
- [Knuth–Morris–Pratt search](../knuth-morris-pratt-algorithm/kmp-search.md)

## Proof depends on

- [Specification of the Aho-Corasick failure and output functions](aho-corasick-failure-and-output.md)
- [Borders and periods of words](borders-and-periods.md)

## Sources

- A. V. Aho and M. J. Corasick, "Efficient String Matching: An Aid to Bibliographic Search", Communications of the ACM 18(6), 1975.
- D. E. Knuth, J. H. Morris Jr. and V. R. Pratt, "Fast Pattern Matching in Strings", SIAM Journal on Computing 6(2), 1977.
