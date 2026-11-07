# (q, r)-Whitney numbers of the first kind

Let $m, r, q$ be complex numbers with
$q \ne 0$, and for a natural number $j$ let $[j]_q = \sum_{i=0}^{j-1} q^i$ be the q-integer.
The (q, r)-Whitney numbers of the first kind $w(n, k) = w_{m,r,q}(n, k)$, for natural numbers
$n$ and $k$, are defined by $w(0, 0) = 1$, $w(0, k + 1) = 0$ and, for all $n$ and $k$,

$$w(n + 1, 0) = -q^{-n} (m [n]_q + r) \, w(n, 0),$$



$$w(n + 1, k + 1) = q^{-n} \bigl( w(n, k) - (m [n]_q + r) \, w(n, k + 1) \bigr).$$

## Sources

- concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`, `jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`, `jis_dd5f8c454fc5760fb197859b`. The source defines these numbers through q-boson operators and proves this recurrence (`identity4`); here the recurrence is the definition.
