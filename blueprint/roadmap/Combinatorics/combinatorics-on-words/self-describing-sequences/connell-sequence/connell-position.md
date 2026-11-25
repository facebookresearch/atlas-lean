# Position of a term in the Connell triangle

For a natural number $r$, the position
$p_n = (j_n, k_n)$ (row $j_n$, zero-based column $k_n$) of index $n \ge 0$ is defined by
$p_0 = (1, 0)$ and $p_{n+1} = (j_n, k_n + 1)$ if $k_n + 1 < 1 + r(j_n - 1)$ (the length of row
$j_n$, with $j_n - 1$ read as $0$ when $j_n = 0$), and $p_{n+1} = (j_n + 1, 0)$ otherwise.
