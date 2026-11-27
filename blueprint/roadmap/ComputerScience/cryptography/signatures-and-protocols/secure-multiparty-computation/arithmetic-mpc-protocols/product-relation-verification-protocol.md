# Verifying product relations between additive shares

Let $q$ be prime. A dealer gives two parties $P_1, P_2$ additive shares $(a_{k1}, b_{k1}, c_{k1})$ and $(a_{k2}, b_{k2}, c_{k2})$ that should satisfy the $m$ *product relations* $c_k = a_k b_k$ for $k = 1, \dots, m$, where $a_k = a_{k1} + a_{k2}$, $b_k = b_{k1} + b_{k2}$ and $c_k = c_{k1} + c_{k2}$. To verify them, the dealer additionally shares random $a_0, b_0$ and, for the polynomials $A(X) = \sum_{k=0}^m a_k L_k(X)$ and $B(X) = \sum_{k=0}^m b_k L_k(X)$ interpolating at fixed points $0, \dots, m$, the coefficients (or evaluations at $2m+1$ points) of a polynomial $C(X)$ of degree $2m$ claimed to equal $A(X)B(X)$, consistent with $c_k = C(k)$ for $1 \le k \le m$. The parties pick a uniform point $r \notin \{0, \dots, m\}$, exchange their shares of $A(r), B(r), C(r)$, and accept iff $A(r)B(r) = C(r)$.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](../semi-honest-mpc-foundations/oracle-aided-protocols-and-perfect-privacy.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
