# Additive $n$-out-of-$n$ secret sharing

Let $G$ be a finite abelian group and $n \ge 2$. Share $z \in G$ among $n$ parties by drawing $\sigma_1, \dots, \sigma_{n-1}$ independently and uniformly from $G$ and setting $\sigma_n = z - \sum_{i<n}\sigma_i$. The full coalition reconstructs $z = \sum_i \sigma_i$, and for every proper coalition $S \subsetneq \{1, \dots, n\}$ the shares $(\sigma_i)_{i \in S}$ are uniform on $G^S$ whatever $z$ is. So only the full coalition learns anything about the secret: this is a perfectly private $n$-out-of-$n$ secret-sharing scheme.

## Proof sketch

If $n \notin S$, the shares of $S$ are among the independent uniform $\sigma_1, \dots, \sigma_{n-1}$. If $n \in S$, some $j < n$ lies outside $S$, and given the other $\sigma_i$ with $i < n$, the share $\sigma_n$ is a translate of $-\sigma_j$, hence uniform. Either way the law of $(\sigma_i)_{i \in S}$ is uniform on $G^S$ and does not depend on $z$.

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
