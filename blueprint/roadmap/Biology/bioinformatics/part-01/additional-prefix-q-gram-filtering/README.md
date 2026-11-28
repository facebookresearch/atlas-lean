# Additional-prefix q-gram filtering

Candidate generation for all-mapper read alignment with an inverted index of genome q-grams. The pigeonhole principle over non-overlapping q-grams of a read gives the classical $k+1$ prefix filter; taking one extra non-overlapping q-gram strengthens it to a "two of $k+2$" filter that returns fewer candidate locations without losing any true mapping.

- [Two-of-(k+2) non-overlapping q-gram filter](two-of-k-plus-2-non-overlapping-q-gram-filter.md)
