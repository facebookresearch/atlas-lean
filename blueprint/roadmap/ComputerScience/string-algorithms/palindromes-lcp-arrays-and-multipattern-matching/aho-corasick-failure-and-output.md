# Specification of the Aho-Corasick failure and output functions

For a finite list $P$ of keywords, identify the states of the Aho-Corasick machine with the prefixes of keywords together with the empty word. After reading a text $t$, the machine is in the state $\lambda(t)$, the longest suffix of $t$ that is a state. The failure function maps a state $u \ne \varepsilon$ to the longest proper suffix of $u$ that is a state, the output of a state $u$ lists the keywords that are nonempty suffixes of $u$, and these satisfy the recurrence that $\lambda(ta)$ equals the goto transition of $\lambda(t)$ on $a$ if defined, and otherwise that of its iterated failures, and $\mathrm{out}(u) = [u \in P] \cup \mathrm{out}(\mathrm{fail}(u))$. Consequently scanning reports exactly the occurrences of keywords in $t$, ordered by end position.

## Depends on

- [Aho–Corasick automaton construction and scanning time](../string-matching-specifications/the-ahocorasick-algorithm.md)

## Sources

- A. V. Aho and M. J. Corasick, "Efficient String Matching: An Aid to Bibliographic Search", Communications of the ACM 18(6), 1975.
