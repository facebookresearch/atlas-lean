# Matrix-chain ordering returns a valid parenthesization

For every $n \ge 1$ and all
natural numbers $p_0, \dots, p_n$, the parenthesization returned by the matrix-chain ordering
algorithm on the dimensions $p_0, \dots, p_n$ is valid: its leaves are the matrices
$0, 1, \dots, n - 1$ in order, each exactly once, and at every multiplication node the column
count of the left factor equals the row count of the right factor, where matrix $i$ has $p_i$
rows and $p_{i+1}$ columns.
