# Cramer–Shoup is CCA secure under DDH and collision resistance

Over a prime-order group $G$, if DDH holds in $G$ and $H'$ is collision resistant, then the Cramer–Shoup scheme with associated data is CCA secure (Boneh and Shoup, Exercise 12.27), in the associated-data form of Boneh and Shoup's Attack Game 12.1 (Section 12.7), where the adversary may interleave several challenge (encryption) queries with its decryption queries. For one challenge query and empty associated data, the scheme is Cramer and Shoup's CS1 (Section 6.1, with $H'$ as its keyed hash $\mathrm{HF}_{hk}$), and their Theorem 1 bounds the guessing advantage $|\Pr[\hat\sigma = \sigma] - \frac12|$ of an adversary making at most $Q$ decryption queries by $\mathrm{AdvDDH} + \mathrm{AdvTCR} + (Q + 4)/q$, where $\mathrm{AdvTCR}$ is a target-collision advantage against the hash, a notion weaker than collision resistance (their Section 5.2). For $Q_e$ challenge queries, the distinguishing advantage equals $Q_e$ times the one-challenge distinguishing advantage of an elementary wrapper adversary (Boneh and Shoup, Theorem 12.1, which carries over to schemes with associated data by Section 12.7).

## Proof sketch

Replace $w = u^\beta$ in the challenge by an independent element (DDH), so the challenge pair is off the Diffie–Hellman pairs. By universal$_2$ hashing, every decryption query with a non-DH pair and a tag different from the challenge tag is rejected except with probability $1/q$; equal tags with a different tuple give a hash collision. Then by universality the mask $v^\sigma w^\tau$ on the challenge is uniform and hides $m_b$.

## Depends on

- [Cramer–Shoup encryption scheme](cramer-shoup-scheme.md)
- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)
- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)
- [Collision resistance and target collision resistance](../../../hash-functions/collision-resistance-and-target-collision-resistance.md)

## Proof depends on

- [Projective hash games against unbounded adaptive adversaries](projective-hash-security-games.md)
- [Fundamental lemma of game playing for stateful oracle handlers](../../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- R. Cramer and V. Shoup, "A Practical Public Key Cryptosystem Provably Secure against Adaptive Chosen Ciphertext Attack", Advances in Cryptology (CRYPTO 1998), LNCS 1462, 1998.
- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003, Sections 5.2 and 6.1, Theorem 1.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Theorem 12.1, Section 12.7 and Exercise 12.27.
