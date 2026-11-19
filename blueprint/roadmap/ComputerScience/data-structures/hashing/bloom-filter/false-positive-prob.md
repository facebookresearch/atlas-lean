# Exact Bloom filter false-positive rate under uniform hashing

Let $m, n, k \in \mathbb{N}$. The exact false-positive rate under uniform hashing, for $m$ bits,
$n$ stored elements and $k$ hash functions, is the fraction of pairs $(H, q)$, where $H$ is a map
from $\{0, \dots, n - 1\} \times \{0, \dots, k - 1\}$ to $\{0, \dots, m - 1\}$ (the stored hash
values) and $q$ is a map from $\{0, \dots, k - 1\}$ to $\{0, \dots, m - 1\}$ (the hash values of
the query), such that every bit $q(j)$ is set by $H$. If there are no pairs $(H, q)$ at all, the
fraction is $0$ (division by zero gives $0$).
