# Correctness of lower-bound search

Let $a = (a_0, \dots, a_{n-1})$ be an array over a linearly
ordered type, sorted in nondecreasing order, let $k$ be a key, and let $\ell$ be the index returned
by lower-bound search for $k$ in $a$. Then $\ell \le n$, $a_j < k$ for every $j < \ell$, and
$k \le a_j$ for every $j$ with $\ell \le j < n$.
