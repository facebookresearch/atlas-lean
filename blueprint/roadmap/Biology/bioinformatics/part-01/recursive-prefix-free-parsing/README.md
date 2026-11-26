# Recursive prefix-free parsing

Prefix-free parsing compresses a highly repetitive text (such as a pangenome collection) into a dictionary of distinct phrases and a parse; applying it again to the parse gives a second-level dictionary and parse. The Burrows–Wheeler transform, the suffix array and the run-sampled LCP array of the original text can all be built from the two dictionaries and the second-level parse alone, in workspace that never touches the first-level parse.

- [BWT from recursive prefix-free parsing](bwt-from-recursive-prefix-free-parsing.md)
- [Suffix array and sampled LCP from recursive prefix-free parsing](suffix-array-and-sampled-lcp-from-recursive-prefix-free-parsing.md)
