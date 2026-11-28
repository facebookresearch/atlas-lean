# Kaplan–Meier influence coefficient

For a cell vector $u$ of event masses $u_{i,c}$ and at-risk masses $u_i$, let $h_i = \sum_cu_{i,c}/u_i$. The Kaplan–Meier influence coefficient at $l$ for the survival at $j$ is $-\prod_{i\le j,\,i\ne l}(1 - h_i)/u_l$ for $l \le j$ and $0$ for $l > j$. Real division and inversion use $x/0 = 0$ and $0^{-1} = 0$.
