# Bottom-up rod cutting

Given prices $p = (p_1, \dots, p_n)$ in an additive commutative
monoid $\alpha$ with a linear order, $p_i$ being the price of a piece of length $i$, bottom-up rod
cutting fills a table $r_0, \dots, r_n$ in increasing order by $r_0 = 0$ and
$r_j = \max_{1 \le i \le j} (p_i + r_{j-i})$ for $1 \le j \le n$, and returns $r_n$. Its cost is
the number of candidates $p_i + r_{j-i}$ it evaluates, one for each pair $1 \le i \le j \le n$.
