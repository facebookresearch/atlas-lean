# ElGamal ciphertexts are unpredictable

Multiplicative ElGamal with exact uniform randomness in a group of prime order $q$ is $1/q$-unpredictable, since the first ciphertext component $g^\beta$ determines $\beta$. With exponents drawn from fair coins within statistical distance $2^{-n}$ of uniform it is $(1/q + 2^{-n})$-unpredictable, hence unpredictable under CDH (which makes $1/q$ negligible). Both multiplicative ElGamal and hybrid ElGamal that hashes the shared secret alone have strongly unpredictable ciphertexts.

## Proof sketch

A ciphertext $c = (v, e)$ is produced only by the unique $\beta$ with $g^\beta = v$; apply the residue-sampling bound to the exponent and the CDH-inverse-order lemma.

## Depends on

- [One-way and unpredictable public-key encryption](one-way-and-unpredictable-pke.md)

## Proof depends on

- [Under CDH the inverse group order is negligible](../../discrete-logarithm-and-diffie-hellman-problems/diffie-hellman-problem-variants-and-attacks/cdh-implies-inverse-order-negligible.md)
- [Sampling residues by reducing uniform bit strings](../../../security-games/probabilistic-oracle-programs/sampling-residues-from-fair-bits.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
