# Mini-array with unary delimiters

A *mini-array* stores $K$ fields of variable bit lengths $s_1, \dots, s_K$ consecutively, together with a delimiter bitmap of $K + \sum_i s_i$ bits that marks each field's end in unary. With rank and select on the delimiter bitmap, the position of field $i$ is found in $O(1)$ time, and a point update rewrites one field and shifts the following bits, supporting small variable-length metadata per slot at a cost of one delimiter bit per field.

## Depends on

- [Rank and select on small bit vectors by table lookup](rank-and-select-by-table-lookup.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
