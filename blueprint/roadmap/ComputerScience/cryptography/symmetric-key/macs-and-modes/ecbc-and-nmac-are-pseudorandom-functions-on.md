# ECBC and NMAC are pseudorandom functions on variable-length messages

Let $\ell$ be a length bound and consider messages of at most $\ell$ blocks, and an adversary making at most $Q$ queries.

- *ECBC.* Let $X = \{0,1\}^n$ with bitwise XOR and $\ell$ polynomially bounded. If $F$ is a secure PRF over $(K, X, X)$ with $|X|$ superpolynomial, the encrypted CBC-MAC $\mathrm{ECBC}_{k_1, k_2}(m) = F(k_2, \mathrm{CBC}_{k_1}(m))$, where $\mathrm{CBC}_{k}(m_1 \cdots m_s)$ sets $t_0 = 0^n$ and $t_i = F(k, t_{i-1} \oplus m_i)$ and outputs $t_s$, is a secure PRF over $(K^2, X^{\le \ell}, X)$: there are PRF adversaries $B_1, B_2$ with

    $$\mathrm{Adv}^{\mathrm{PRF}}[A, \mathrm{ECBC}] \le \mathrm{Adv}^{\mathrm{PRF}}[B_1, F] + \mathrm{Adv}^{\mathrm{PRF}}[B_2, F] + \frac{(Q(\ell + 1))^2 + Q^2}{2|X|}.$$

- *NMAC.* Let $F$ be a secure PRF over $(K, X, K)$ and let $g : K \to X$ be an efficiently computable injection. The cascade $\mathrm{Cascade}_{k}(m_1 \cdots m_s)$ sets $t_0 = k$ and $t_i = F(t_{i-1}, m_i)$ and outputs $t_s$, and the nested MAC is $\mathrm{NMAC}_{k_1, k_2}(m) = F(k_2, g(\mathrm{Cascade}_{k_1}(m)))$. It is a secure PRF over $(K^2, X^{\le \ell}, K)$: there are PRF adversaries $B_1, B_2$ with

    $$\mathrm{Adv}^{\mathrm{PRF}}[A, \mathrm{NMAC}] \le Q(\ell + 1)\cdot \mathrm{Adv}^{\mathrm{PRF}}[B_1, F] + \mathrm{Adv}^{\mathrm{PRF}}[B_2, F] + \frac{Q^2}{2|K|}.$$

The raw CBC-MAC is not a secure PRF on variable-length messages: from the tag $t$ of a one-block message $m$, the two-block message $(m, m \oplus t)$ has tag $t$ as well.

## Expansion

This page collects several results; it becomes ready once each is stated separately:

- Security of ECBC, as a page of its own
- Security of NMAC, as a page of its own
- Insecurity of the raw CBC-MAC on variable-length messages, as a page of its own

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Polynomial-query unforgeability of MACs](../../security-games/asymptotic-security/poly-query-macsecure.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorems 6.6 and 6.7, and Section 7.3 (their derivation from PRF(UHF) composition)
- M. Bellare, R. Canetti and H. Krawczyk, "Keying hash functions for message authentication", *CRYPTO 1996*, LNCS 1109, Springer, 1996
