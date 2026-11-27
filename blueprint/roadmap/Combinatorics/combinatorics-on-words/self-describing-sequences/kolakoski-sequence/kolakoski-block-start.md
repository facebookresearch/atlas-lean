# Starting positions of Kolakoski blocks

For a sequence $K_1, K_2, K_3, \ldots$ of natural
numbers, the starting positions $s_n$ of its blocks are defined by $s_1 = 1$ and
$s_{n+1} = s_n + K_n$ for every $n \ge 1$, together with the convention $s_0 = 0$.

Block $n$ of a candidate Kolakoski sequence $K$ consists of the positions $i$ with
$s_n \le i < s_n + K_n$; index $0$ lies outside the one-indexed sequence.
