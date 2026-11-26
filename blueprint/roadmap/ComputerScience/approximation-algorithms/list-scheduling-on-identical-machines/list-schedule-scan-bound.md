# Invariant bound for list scheduling

Let $m \ge 1$ and $a, b, M \in \mathbb{N}$. Let
$\sigma$ assign job lists to the $m$ machines so that $\sigma$ is a schedule of a list $P$ of
jobs already placed, let $L(i)$ be the sum of $\sigma(i)$ for each machine $i$, and let $R$ be a
list of remaining jobs. Assume that $a$ times the makespan of $\sigma$ is at most $bM$. Assume
also that whenever $P$ followed by $R$ equals $P'$ followed by a job $p$ followed by a list
$R'$, and $\sigma'$ is any schedule of $P'$ with loads $L'(i)$ equal to the sum of
$\sigma'(i)$, we have $a(L'(k) + p) \le bM$, where $k$ is the least-loaded machine for $L'$.
Then list scheduling of $R$ started from the loads $L$ and machine lists $\sigma$ produces a
schedule whose makespan $C$ satisfies $aC \le bM$.
