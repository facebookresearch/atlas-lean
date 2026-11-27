# Binary search is logarithmic

For every test $p$ on natural numbers and all $lo, hi \in \mathbb{N}$, the number of probes of the
binary search for $p$ on $lo, hi$ is at most $\lfloor \log_2 (hi - lo) \rfloor + 1$, where
$hi - lo$ is $0$ when $hi \le lo$ and $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
