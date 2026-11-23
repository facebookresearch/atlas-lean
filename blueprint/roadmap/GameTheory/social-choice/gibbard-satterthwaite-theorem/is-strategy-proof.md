# Strategy-proof social choice function

For a strict total order $P$, write $x \succ_P y$
when $x$ is related to $y$ by $P$ ($P$ ranks $x$ above $y$). A resolute social choice function $F$
is strategy-proof when, for all profiles $p_1$, $p_2$ and every voter $i$ such that $p_1(j) =
p_2(j)$ for all voters $j \ne i$, it is not the case that $F(p_2) \succ_{p_1(i)} F(p_1)$: no voter
gains by misreporting alone, judged by the true order $p_1(i)$.
