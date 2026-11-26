# Correctness hop for salted implicit-rejection Fujisaki–Okamoto transforms

In a salted Fujisaki–Okamoto KEM with implicit rejection, a single joint random-oracle query $G(m, \text{salt}, pk)$ returns both the session key and the encryption coins. Fix a key pair. The real decapsulation handler (decrypt, re-encrypt, compare) and a keyless handler that answers decapsulation queries only from cached oracle queries have output laws within

$$
(q_{RO} + q_D)\cdot \delta_{\max}(pk, sk)
$$

for an adversary making $q_{RO}$ oracle and $q_D$ decapsulation queries, where $\delta_{\max}$ is the worst-message decryption failure probability of the key pair; averaging over key generation (the common key-mixture rule) gives a bound of $(q_{RO} + q_D)\,\delta$ for a $\delta$-correct scheme, also for randomized adversaries receiving the full public challenge.

## Proof sketch

The two handlers agree as long as every cached honest encryption decrypts to its cached message; each joint query creates one such entry, which fails with probability at most $\delta_{\max}$.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)

## Proof depends on

- [Correctness of the Fujisaki–Okamoto KEMs](fo-kem-correctness.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
