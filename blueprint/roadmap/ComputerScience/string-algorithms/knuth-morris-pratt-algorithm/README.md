# Knuth–Morris–Pratt algorithm

## The search

- [Knuth–Morris–Pratt search](kmp-search.md)
- [KMP returns the first match](kmp-search-eq-some-iff.md)
- [KMP finds no match exactly when no offset matches](kmp-search-eq-none-iff.md)
- [KMP finds no match exactly when the pattern does not occur](kmp-search-eq-none-iff-not-is-infix.md)
- [KMP search agrees with the first-infix split](kmp-search-eq-drop-infix-map-length.md)
- [KMP search makes linearly many comparisons](kmp-search-time-le.md)
- [KMP search on the empty pattern](kmp-search-nil-pattern.md)

## The prefix table

- [The KMP prefix table](prefix-table.md)
- [Size of a KMP prefix table](size.md)
- [Extending a KMP prefix table by one symbol](extend.md)
- [Building the KMP prefix table of a pattern](mk-prefix-table.md)
- [Transition function of the KMP matcher](step.md)
- [Size of the KMP prefix table](mk-prefix-table-size.md)
- [The KMP prefix table stores the pattern](mk-prefix-table-symbols.md)
- [The KMP failure function](mk-prefix-table-failure-spec.md)
- [Correctness of the KMP transition](mk-prefix-table-step-spec.md)

## Sources

- D. E. Knuth, J. H. Morris, Jr. and V. R. Pratt, "Fast pattern matching in strings", *SIAM J.
  Comput.* 6(2) (1977) 323–350, DOI 10.1137/0206024.
