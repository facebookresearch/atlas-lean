# Split candidates evaluated by matrix-chain ordering

For every $n \ge 1$ and all natural
numbers $p_0, \dots, p_n$, the matrix-chain ordering algorithm run on the dimensions
$p_0, \dots, p_n$ evaluates exactly $\binom{n+1}{3}$ split candidates.

This is the number of triples $i \le k < j < n$, so the dynamic program evaluates one candidate
for every interval split.
