# Burrows–Wheeler transform of repetitive collections

The Burrows–Wheeler transform (BWT) and FM-index underlie read aligners and pangenome indexes; building the BWT of very large, highly repetitive genome collections needs workspace proportional to their distinct content rather than their length. The LF mapping and backward search used throughout are [LF-mapping from the last column](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/lf.md), [LF in suffix-array terms](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/suffix-array-get-d-lf.md) and [FM-index backward search](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/backward-search.md).

- [Prefix-free parse of a text](prefix-free-parse-of-a-text.md)
- [BWT from a prefix-free parse](bwt-from-a-prefix-free-parse.md)
