# Probability that a given Bloom filter bit is unset

Let $m, n, k \in \mathbb{N}$ with $m > 0$ and $i \in \{0, \dots, m - 1\}$. The fraction of maps
$H$ from $\{0, \dots, n - 1\} \times \{0, \dots, k - 1\}$ to $\{0, \dots, m - 1\}$ that never take
the value $i$ is $(1 - 1/m)^{n k}$. So under uniform hashing a given bit is unset with
probability $(1 - 1/m)^{n k}$.
