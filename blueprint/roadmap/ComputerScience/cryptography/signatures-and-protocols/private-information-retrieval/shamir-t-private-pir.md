# Polynomial-interpolation $t$-private PIR

Let $\mathbb{F}$ be a finite field with $|\mathbb{F}| > |S|$, and arrange the database as a $d$-dimensional cube with side $m$, $n \le m^d$. The user Shamir-shares (with threshold $t$) each coordinate of the indicator vectors $e_{i_1}, \dots, e_{i_d} \in \mathbb{F}^m$ and sends server $s$ its shares; server $s$ returns the evaluation of the degree-$d$ multilinear polynomial $\sum_{j} x_j \prod_r e_{i_r}(j_r)$ on its shares, which is a share of $x_i$ under a polynomial of degree $dt$. If $|S| \ge dt + 1$, Lagrange interpolation at $0$ recovers $x_i$, so the scheme is perfectly correct; it is $t$-private, since any $t$ servers see uniformly random shares; and it is not $(t + 1)$-private in general. For $d = 2$ (matrix balancing, $n \le m^2$) the communication is $|S|(2m + 1)\lceil\log_2|\mathbb{F}|\rceil$ bits ($2m$ query elements and one answer element per server), and for general $d$ it is $O(|S|\, d\, n^{1/d} \log|\mathbb{F}|)$.

## Proof sketch

The answer polynomial is the composition of a degree-$d$ multilinear form with degree-$t$ sharing polynomials, so it has degree at most $dt$ and evaluates at $0$ to $x_i$. Privacy is the marginal uniformity of Shamir shares for coalitions of size at most $t$; with $t + 1$ servers the shares of a known index distribution are not uniform.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)
- [Shamir threshold secret sharing](../secure-multiparty-computation/secret-sharing-schemes/shamir-secret-sharing.md)

## Proof depends on

- [Linearity, multiplicativity and privacy of Shamir sharing](../secure-multiparty-computation/secret-sharing-schemes/shamir-sharing-properties.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
- Adi Shamir, "How to Share a Secret", Communications of the ACM, 1979.
