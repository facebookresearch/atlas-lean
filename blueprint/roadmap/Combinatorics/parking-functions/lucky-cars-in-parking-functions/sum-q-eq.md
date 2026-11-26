# Number of parking functions in which a given car is lucky

Number cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and parks there. Then for every $n$ and every car $i < n$,

$$\sum_{j=0}^{n-1} q_n(i, j) = (n + 1 - i)(n + 1)^{n-2},$$

an identity in $\mathbb{Q}$ (for $n = 1$ the exponent is $-1$). The left side is the number of
parking functions of length $n$ in which car $i$ is lucky; in the paper's one-based numbering
the count for the $i$-th car is $(n + 2 - i)(n + 1)^{n-2}$.

## Sources

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats, "Lucky Cars and Lucky Spots in Parking Functions", Journal of Integer Sequences 29 (2026), Article 26.1.1, Corollary 10.
