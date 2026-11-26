# Soundness of product-relation verification against a corrupt dealer

In the product-relation verification protocol with $m$ relations over $\mathbb{Z}_q$, $q$ prime, if the dealer is corrupt (its messages to $P_1$ and $P_2$ are arbitrary) and both parties are honest, and some relation $c_k = a_k b_k$ with $1 \le k \le m$ fails, then the honest parties accept with probability at most

$$
\frac{2m}{q - m - 1}.
$$

With an honest dealer, the discrepancy polynomial $A(X)B(X) - C(X)$ vanishes identically, so the honest parties always accept.

## Proof sketch

If some relation fails, the discrepancy polynomial $A(X)B(X) - C(X)$ of degree at most $2m$ is nonzero (it does not vanish at that $k$), so it has at most $2m$ roots; the challenge is uniform among the $q - m - 1$ points outside $\{0, \dots, m\}$.

## Depends on

- [Verifying product relations between additive shares](product-relation-verification-protocol.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
