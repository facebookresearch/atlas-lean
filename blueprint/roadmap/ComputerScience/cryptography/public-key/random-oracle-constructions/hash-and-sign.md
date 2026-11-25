# Hash-and-sign

Let $\mathcal{S} = (G, S, V)$ be a signature scheme over $(M, \Sigma)$ that is secure (existentially unforgeable under chosen-message attacks).

**Collision-resistant hashing.** If $H : K_H \times M' \to M$ is a collision-resistant keyed hash family, the scheme whose key generation also samples a uniform key $k_H \in K_H$ and includes it in the public verification key, which signs $m \in M'$ by $S(sk, H(k_H, m))$ and verifies by
$V(pk, H(k_H, m), \sigma)$, is secure: for every signature adversary $A$ there are an efficient signature adversary $B_S$ and an efficient collision finder
$B_H$, elementary wrappers around $A$, with

$$\mathrm{SIGadv}[A, \mathcal{S}'] \le \mathrm{SIGadv}[B_S, \mathcal{S}] + \mathrm{CRadv}[B_H, H].$$

**Target-collision-resistant hashing.** If $H$ is a target-collision-resistant keyed hash function over $(K_H, M', T)$ and $\mathcal{S}$ signs messages in
$K_H \times T$, the scheme that signs $m$ by choosing $r \in K_H$ uniformly at random and outputting $(\sigma, r)$ with $\sigma = S(sk, (r, H(r, m)))$, and verifies by
$V(pk, (r, H(r, m)), \sigma)$, is secure: for every adversary $A$ making at most $Q$ signing queries there are efficient $B_S$ and $B_H$ with

$$\mathrm{SIGadv}[A, \mathcal{S}'] \le \mathrm{SIGadv}[B_S, \mathcal{S}] + Q \cdot \mathrm{TCRadv}[B_H, H].$$

## Depends on

- [Polynomial-query unforgeability of signatures](../../security-games/asymptotic-security/poly-query-sig-secure.md)
- [Collision resistance and target collision resistance](../../hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>: Section 13.2, construction (13.1) and Theorem 13.1 (collision-resistant hashing), and Section 13.2.1, construction (13.2) and Theorem 13.2 (target-collision-resistant hashing).
