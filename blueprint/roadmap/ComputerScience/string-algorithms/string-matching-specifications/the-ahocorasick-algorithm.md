# Aho–Corasick automaton construction and scanning time

For a finite set $\mathcal{P}$ of patterns over a fixed finite alphabet, the Aho–Corasick automaton (the trie of $\mathcal{P}$ with failure links to the longest proper suffix that is a trie node and output links to pattern-ending suffixes) can be built in $O(\sum_{p \in \mathcal{P}} |p|)$ time, and scanning a text $t$ with it, following output links at each position, takes $O(|t| + \#\mathrm{occ})$ time, where $\#\mathrm{occ}$ is the number of occurrences of patterns of $\mathcal{P}$ in $t$.

## Depends on

- [Pattern match at an offset](../string-matching-problem/match-at.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- A. V. Aho and M. J. Corasick, "Efficient string matching: an aid to bibliographic search", *Communications of the ACM* 18(6):333–340, 1975
