# Running time of greedy set cover

Let $F$ be a list of finite sets and $U$ a finite set.
The running time of greedy set cover of $U$ from $F$ is at most
$(|U| + 1)(|F| + \sum_{S \in F} |S|)$, where $|F|$ is the length of the list and the sum runs
over the entries of $F$, counted with repetition.

There are at most $|U| + 1$ searches for a best set, each costing $|F| + \sum_{S \in F} |S|$.
