# Three-message DDH oblivious transfer and the necessity of its consistency check

Let $\mathbb{G}$ be a cyclic group of prime order $q$ with generator $g$, written additively. In the three-message (Bellare–Micali style) protocol, the sender sends a uniform $u \in \mathbb{G}$; the receiver with choice $c$ draws a uniform exponent $\beta$, sets $w_c = \beta g$ and $w_{1-c} = u - w_c$, and sends $(w_0, w_1)$; the sender checks $w_0 + w_1 = u$, draws one fresh uniform exponent $\rho$ and returns $(\rho g, \rho w_0 + m_0, \rho w_1 + m_1)$, ElGamal-style encryptions of $m_0 \in \mathbb{G}$ under the public key $w_0$ and of $m_1 \in \mathbb{G}$ under $w_1$ sharing the randomness $\rho$; the receiver decrypts the $c$-th with $\beta$. Then: (i) the receiver always outputs $m_c$ and the sender outputs nothing; (ii) against a corrupted sender the receiver's choice is perfectly hidden when $\beta$ is uniform in $\mathbb{Z}_q$: whatever $u$ is, $(w_0, w_1)$ is a uniform pair summing to $u$ for both values of $c$ (if $\beta$ is instead a uniform $n$-bit integer reduced modulo $q$, the pairs for $c = 0$ and $c = 1$ are within statistical distance $q/2^n$); (iii) against a semi-honest receiver, security reduces by an explicit polynomial-time reduction to the decisional Diffie–Hellman assumption, because $u$ is uniform and the receiver knows only the discrete logarithm $\beta$ of $w_c$, so $(\rho g, \rho w_{1-c})$ masks $m_{1-c}$ by DDH; the check blocks the attack in (iv) but does not by itself yield a proof of security against malicious receivers; (iv) if the sender omits the check $w_0 + w_1 = u$, a malicious receiver sends $w_0 = \beta_0 g$ and $w_1 = \beta_1 g$ with both exponents known and recovers both messages.

## Proof sketch

(ii) $\beta g$ is uniform, so both choices give the uniform pair summing to $u$. (iii) For a semi-honest receiver, $w_{1-c} = u - \beta g$ is a uniform group element independent of $\beta$, so given the receiver's view $(\rho g, \rho w_{1-c})$ is pseudorandom by DDH and hides $m_{1-c}$. (iv) Without the check both keys can be chosen with known exponents.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)
- [DDH advantage of the distinguisher built from a CDH solver](../../../public-key/hardness-assumptions/ddh-advantage-ddh-of-cdh.md)

## Proof depends on

- [ElGamal as a public-key encryption scheme](../../../public-key/cpa-security-of-elgamal/scheme.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Moni Naor and Benny Pinkas, "Efficient Oblivious Transfer Protocols", Proceedings of the Twelfth Annual ACM-SIAM Symposium on Discrete Algorithms, 2001.
