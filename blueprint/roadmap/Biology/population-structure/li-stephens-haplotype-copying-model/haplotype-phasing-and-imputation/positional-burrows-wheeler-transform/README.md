# Positional Burrows–Wheeler transform

Data structures that keep a panel of haplotypes sorted, at every variant site, by their reversed prefixes, so that haplotypes sharing long matches ending at a site are adjacent. They are built in one linear sweep and give constant-time access to long identical-by-state matches, used to choose small conditioning sets of haplotypes for haplotype-copying models in phasing and imputation.

- [Syllable PBWT and rolling-hash long-match queries](syllable-pbwt-and-rolling-hash-long-match-queries.md)
