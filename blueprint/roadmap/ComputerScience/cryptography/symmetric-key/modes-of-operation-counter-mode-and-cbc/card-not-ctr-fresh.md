# Few challenge counters overlap the query counters

Let $N > 0$ and $q, \ell \in \mathbb{N}$. For every choice of query counters $\rho \in (\mathbb{Z}/N)^q$, the number of challenge counters $r_s \in \mathbb{Z}/N$ that are not [fresh](ctr-fresh.md), that is, for which $\rho_j + i' = r_s + i$ in $\mathbb{Z}/N$ for some $j < q$ and some $i, i' < \ell$, is at most

$$
q \cdot \max(2\ell - 1, 0).
$$

At $\ell = 0$ every challenge counter is fresh and the bound is $0$. No group structure on the blocks is involved.
