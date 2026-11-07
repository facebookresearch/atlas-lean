# Table cost of the edit distance algorithm

For lists $s$ and $t$ over a type with a
Boolean equality test, write $|s|$ and $|t|$ for their lengths. The number of table-cell
transitions charged by the dynamic-programming edit distance algorithm on $s$ and $t$ is exactly
$(|s| + 1)(|t| + 1)$, one per pair of a prefix of $s$ and a prefix of $t$.
