# Partition-sum expansion of $\binom{nm}{l}$, unconditional form

For all natural numbers $n$,
$m$ and $l$, let $P$ be the set of tuples $s = (s_1, \dots, s_m)$ of natural numbers with
$\sum_{j=1}^{m} j\,s_j = l$, and for $s \in P$ write $T_j(s) = s_{j+1} + \dots + s_m$. Then

$$\binom{nm}{l} = \sum_{s \in P} \prod_{j=1}^{m} \binom{n - T_j(s)}{s_j} \binom{m}{j}^{s_j},$$

where $n - T_j(s)$ is read as $0$ when $T_j(s) > n$. No positivity or range conditions on $n$,
$m$ and $l$ are needed.
