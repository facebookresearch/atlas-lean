# A universal family has a member with few collisions

Let $K$ be a finite set of $n$ keys, let $m > 0$, and let $(h_i)_{i \in s}$ be a universal
family of functions $K \to \{0, \dots, m - 1\}$ indexed by a finite nonempty set $s$
(for distinct keys $x \ne y$, at most $|s| / m$ indices $i \in s$ satisfy
$h_i(x) = h_i(y)$). Then some $i \in s$ satisfies

$$m \sum_{b} n_b (n_b - 1) \le n (n - 1),$$

where $n_b$ is the number of keys that $h_i$ sends to bucket $b$. The sum counts the ordered
pairs of distinct keys sent to the same bucket.
