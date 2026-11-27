# Potential bound for weighted greedy set cover

Let $F$ be a list of finite sets, $U$ a
finite set and $w$ a rational cost function on finite sets with $w(S) \ge 0$ for every $S$ in $F$.
If $C^*$ is a list of sets from $F$ whose union contains $U$, then the weighted greedy set cover of
$U$ from $F$ with costs $w$ has total cost at most $\sum_{S \in C^*} w(S)\, H(|S \cap U|)$, the sum
running over the entries of $C^*$ with repetition, where
$H(n) = 1 + \frac{1}{2} + \dots + \frac{1}{n}$ is the $n$-th harmonic number.
