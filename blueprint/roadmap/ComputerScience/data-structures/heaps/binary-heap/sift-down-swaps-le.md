# Sift-down performs at most one swap per remaining level

Write $|a|$ for the size of an
array $a$, and let $\ell(n) = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $\ell(0) = 0$. For
every array $a$ over a linearly ordered type and every index $i$, the number of array swaps
counted by timed sift-down from $i$ is at most $\max(0, \ell(|a|) - \ell(i+1))$.
