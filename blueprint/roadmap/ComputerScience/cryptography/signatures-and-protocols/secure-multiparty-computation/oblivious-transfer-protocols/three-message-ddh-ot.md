# Three-message DDH oblivious transfer and the necessity of its consistency check

Let $\mathbb{G}$ be a cyclic group of prime order $q$ with generator $g$, written additively. In the three-message (Bellare–Micali style) protocol, the sender sends a uniform $u \in \mathbb{G}$; the receiver with choice $c$ draws a uniform exponent $\beta$, sets $w_c = \beta g$ and $w_{1-c} = u - w_c$, and sends $(w_0, w_1)$; the sender checks $w_0 + w_1 = u$ and returns ElGamal-style encryptions of $m_0$ under the public key $w_0$ and of $m_1$ under $w_1$, with fresh randomness; the receiver decrypts the $c$-th with $\beta$. Then: (i) the receiver always outputs $m_c$ and the sender outputs nothing; (ii) against a corrupted sender the protocol is statistically secure: $(w_0, w_1)$ is a uniform pair summing to $u$ whatever $c$, up to $2^{-n}$ when exponents are sampled from $n$ fair bits; (iii) against a corrupted receiver, security reduces by an explicit polynomial-time reduction to the decisional Diffie–Hellman assumption, because the receiver cannot know the discrete logarithms of both $w_0$ and $w_1$ without knowing that of $u$; (iv) if the sender omits the check $w_0 + w_1 = u$, a malicious receiver sends $w_0 = \beta_0 g$ and $w_1 = \beta_1 g$ with both exponents known and recovers both messages.

## Proof sketch

The check forces at least one of $w_0, w_1$ to be a group element whose discrete logarithm relative to the public element the receiver cannot know, so that encryption under it is pseudorandom by DDH; without the check both keys can be chosen with known exponents.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)
- [DDH advantage of the distinguisher built from a CDH solver](../../../public-key/hardness-assumptions/ddh-advantage-ddh-of-cdh.md)

## Proof depends on

- [ElGamal as a public-key encryption scheme](../../../public-key/cpa-security-of-elgamal/scheme.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Moni Naor and Benny Pinkas, "Efficient Oblivious Transfer Protocols", Proceedings of the Twelfth Annual ACM-SIAM Symposium on Discrete Algorithms, 2001.
