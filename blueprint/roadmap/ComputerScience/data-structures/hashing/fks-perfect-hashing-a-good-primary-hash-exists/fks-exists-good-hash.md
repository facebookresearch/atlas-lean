# FKS primary hash

**FKS primary hash** (CLRS, Section 11.5). Let $K$ be a finite set of $n > 0$ keys and let
$(h_i)_{i \in s}$ be a universal family of functions $K \to \{0, \dots, n - 1\}$ indexed by a
finite nonempty set $s$. Then some $i \in s$ has fewer than $n$ ordered collisions,
$\sum_b n_b (n_b - 1) < n$, and its squared bucket sizes satisfy $\sum_b n_b^2 < 2n$, where
$n_b$ is the number of keys that $h_i$ sends to bucket $b$. With secondary tables of sizes
$n_b^2$, the two-level scheme then uses linear total space.
