# Weighted greedy set cover

Let $F = [S_1, \dots, S_n]$ be a list of finite sets, $U$ a
finite set and $w$ a function giving each finite set $S$ a rational cost $w(S)$. The weighted
greedy set cover of $U$ from $F$ with costs $w$ is computed as follows. If no $S_i$ meets $U$,
the result is the empty list. Otherwise let $T$ be the first $S_i$ in the list with
$S_i \cap U \ne \emptyset$ that minimizes $w(S_i) / |S_i \cap U|$ among the sets of $F$ meeting
$U$; the result is $T$ followed by the weighted greedy set cover of $U \setminus T$ from $F$ with
costs $w$. Each step, including the last one, costs $n + |S_1| + \dots + |S_n|$.
