# Effect of one bubble pass

Let $w$ be an input on $n$ wires with values in a linearly
ordered type, let $m < n$, and let $w'$ be the output of the bubble pass ending at wire $m$
(the comparators $(0, 1), \ldots, (m - 1, m)$) run on $w$. Then $w'_i = w_i$ for every wire
$i > m$; $w'_i \le w'_m$ for every wire $i \le m$; and for every wire $i \le m$ there is a wire
$j \le m$ with $w'_i = w_j$.
