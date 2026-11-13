# Sift-up restores $d$-ary heap order

Let $a$ be an array over a linearly ordered type,
of length $|a|$ with entries $a_0, \dots, a_{|a|-1}$, let $d$ and $i$ be natural numbers, and
write $p(j) = \lfloor (j-1)/d \rfloor$ for the parent of an index $j > 0$. Suppose $a$ is ready
for sift-up at $i$: $d \ge 2$, $i < |a|$, $a_{p(j)} \le a_j$ for every $0 < j < |a|$ with
$j \ne i$, and, if $i > 0$, $a_{p(i)} \le a_j$ for every $0 < j < |a|$ with $p(j) = i$. Then the
array $b$, of length $|b|$ with entries $b_0, \dots, b_{|b|-1}$, obtained from $a$ by $d$-ary
sift-up from index $i$ is $d$-ary heap ordered: $b_{p(j)} \le b_j$ for every $0 < j < |b|$.
