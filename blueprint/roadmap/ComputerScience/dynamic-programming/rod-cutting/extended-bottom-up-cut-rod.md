# Extended bottom-up rod cutting

Let $\alpha$ be an additive commutative monoid with a
linear order, and let $p_1, \dots, p_n \in \alpha$ be the prices of pieces of length
$1, \dots, n$ (the price vector's entry $i - 1$ is $p_i$). The algorithm fills a revenue table
$r_0, \dots, r_n$ and a first-cut table $s_1, \dots, s_n$ for the lengths $j = 0, 1, \dots, n$ in
increasing order: $r_0 = 0$, and for $j \ge 1$ it scans the candidates $p_i + r_{j-i}$ for
$i = 1, \dots, j$ in increasing order of $i$, starting from the candidate for $i = 1$ and moving
to a later candidate only when it is strictly larger than the current one. Then $r_j$ is the
largest candidate and $s_j$ is the least $i$ whose candidate equals $r_j$. The result is the pair
of tables, where $r_j$ is the revenue vector's entry $j$ and $s_j$ is the cut vector's entry
$j - 1$, and the cost is one tick per evaluated candidate, so $j$ ticks for length $j$.
