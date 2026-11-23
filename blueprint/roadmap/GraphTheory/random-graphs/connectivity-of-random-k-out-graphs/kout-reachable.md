# Reachability by a chain of friends

Let $c$ assign to each person $i$ among $N$ people a
set $c(i)$ of people, the friends of $i$. A person $b$ is reachable from a person $a$ if there are
$m \ge 0$ and people $p_0 = a, p_1, \dots, p_m = b$ such that for each $j < m$, $p_j$ is a friend
of $p_{j+1}$ or $p_{j+1}$ is a friend of $p_j$.
