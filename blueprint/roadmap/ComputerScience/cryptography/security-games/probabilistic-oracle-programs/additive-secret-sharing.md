# Additive secret sharing over a finite abelian group

Let $G$ be a finite abelian group and $m \ge 1$. To share a secret $s \in G$ among $m$ parties, the *additive secret sharing* scheme samples $r_1, \dots, r_{m-1}$ independently and uniformly from $G$ and outputs the shares $(r_1, \dots, r_{m-1}, r_m)$ with $r_m = s - \sum_{j<m} r_j$. Reconstruction adds all shares: $\sum_{j=1}^m r_j = s$.

## Depends on

- [Verifiable secret sharing](../../signatures-and-protocols/secure-multiparty-computation/verifiable-secret-sharing.md)

## Sources

- R. Cramer, I. Damgård and J. B. Nielsen, "Secure Multiparty Computation and Secret Sharing", Cambridge University Press, 2015.
- A. Shamir, "How to Share a Secret", Communications of the ACM 22(11), 1979.
