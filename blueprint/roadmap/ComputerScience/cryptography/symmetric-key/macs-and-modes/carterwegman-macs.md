# Carter–Wegman MACs

Let $H$ be a keyed hash function over $(K_H, M, T)$ with $T = \mathbb{Z}_N$. In the *difference unpredictability* game the challenger picks a uniformly random key $k$ and the adversary outputs distinct $m_0, m_1 \in M$ and $\delta \in T$; it wins if $H(k, m_1) - H(k, m_0) = \delta$. $H$ is an *$\varepsilon$-DUF* if every adversary, even an inefficient one, wins with probability at most $\varepsilon$, and a *computational DUF* if every efficient adversary wins with negligible probability.

- *Polynomial hashing.* For a prime $p$ and a length bound $\ell$, the hash $H_{\mathrm{poly}}(k, (a_1, \dots, a_v)) = k^v + a_1 k^{v-1} + \cdots + a_v$ over $(\mathbb{Z}_p, \mathbb{Z}_p^{\le \ell}, \mathbb{Z}_p)$ is an $(\ell/p)$-UHF, and $H_{\mathrm{xpoly}}(k, (a_1, \dots, a_v)) = k^{v+1} + a_1 k^v + \cdots + a_v k$ is an $((\ell + 1)/p)$-DUF.
- *PRF(UHF) composition.* If $H$ over $(K_H, M, X)$ is a computational UHF and $F$ over $(K_F, X, T)$ is a secure PRF, then $F'((k_1, k_2), m) = F(k_2, H(k_1, m))$ is a secure PRF: for every PRF adversary $A$ making at most $Q$ queries there are adversaries $B_F$, $B_H$ with

    $$\mathrm{PRFadv}[A, F'] \le \mathrm{PRFadv}[B_F, F] + \frac{Q^2}{2} \cdot \mathrm{UHFadv}[B_H, H].$$

- *Carter–Wegman MAC.* Let $F$ be a secure PRF over $(K_F, R, T)$ with $|R|$ superpolynomial and $H$ a computational DUF over $(K_H, M, T)$. The MAC tags $m$ with $(r, H(k_1, m) + F(k_2, r))$ for a fresh uniformly random $r \in R$, and it is a secure MAC: for every MAC adversary $A$ making at most $Q$ signing queries there are adversaries $B_F$, $B_H$ with

    $$\mathrm{MACadv}[A] \le \mathrm{PRFadv}[B_F, F] + \mathrm{DUFadv}[B_H, H] + \frac{Q^2}{2|R|} + \frac{1}{|T|}.$$

  The difference condition cannot be weakened to universality: instantiated with $H_{\mathrm{poly}}$ the Carter–Wegman MAC is insecure.
- *One-time MACs.* $H$ over $(K, M, T)$ is an *$\varepsilon$-PUF* (pairwise unpredictable) if no adversary, even an inefficient one, that learns $H(k, m_0)$ for one message $m_0$ of its choice can output $m_1 \ne m_0$ and $H(k, m_1)$ with probability above $\varepsilon$. If $H$ is an $\varepsilon$-DUF over $T = \mathbb{Z}_N$, then $H'((k_1, k_2), m) = H(k_1, m) + k_2$ is an $\varepsilon$-PUF, and the MAC that tags $m$ with $H(k, m)$ for an $\varepsilon$-PUF $H$ is unconditionally secure for one message: every adversary allowed one signing query forges with probability at most $\varepsilon$. In particular the Carter–Wegman MAC with a truly random pad in place of the PRF is an unconditionally secure one-time MAC.

## Expansion

This page collects several results; it becomes ready once each is stated separately:

- Polynomial hashing as a universal and a difference-unpredictable hash, as a page of its own
- The PRF(UHF) composition bound, as a page of its own
- Security of the Carter–Wegman MAC, as a page of its own

## Depends on

- [Bounded universal hash functions](../../hash-functions/bounded-universal-hash-functions.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Polynomial-query unforgeability of MACs](../../security-games/asymptotic-security/poly-query-macsecure.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Lemmas 7.2, 7.8 and 7.11, Theorems 7.7, 7.9 and 7.12, Definitions 7.5 and 7.7, and Remark 7.5
- Original construction, with one-time pads in place of the PRF: M. N. Wegman and J. L. Carter, "New hash functions and their use in authentication and set equality", *Journal of Computer and System Sciences* 22(3):265–279, 1981. Boneh and Shoup name the construction after Carter and Wegman.
