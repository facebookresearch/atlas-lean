# Perfect privacy of additive secret sharing

In additive secret sharing over a finite abelian group $G$ with $m$ parties, for every secret $s \in G$ and every set $T$ of at most $m-1$ party indices, the joint distribution of the shares $(r_j)_{j \in T}$ is uniform on $G^{T}$; in particular it does not depend on $s$. Moreover, for every secret the full share vector is uniform on the coset $\{(r_1, \dots, r_m) : \sum_j r_j = s\}$.

## Proof sketch

For a missing index $j_0 \notin T$, the map from $(r_j)_{j \ne j_0}$ to the shares is a bijection of $G^{m-1}$ onto the shares indexed by $[m]\setminus\{j_0\}$, because the last share is a translate by $s$; uniform inputs therefore give uniform shares, and projecting to $T$ preserves uniformity.

## Depends on

- [Additive secret sharing over a finite abelian group](additive-secret-sharing.md)

## Sources

- R. Cramer, I. Damgård and J. B. Nielsen, "Secure Multiparty Computation and Secret Sharing", Cambridge University Press, 2015.
