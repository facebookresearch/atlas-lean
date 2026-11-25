# Running time of weighted greedy set cover

Let $F = [S_1, \dots, S_m]$ be a list of finite
sets, $U$ a finite set and $w$ a rational cost function on finite sets. The weighted greedy set
cover of $U$ from $F$ with costs $w$ runs in time at most
$(|U| + 1)\,(m + |S_1| + \dots + |S_m|)$: at most $|U| + 1$ searches for a best set, each costing
$m$ plus the total size of the sets of $F$.
