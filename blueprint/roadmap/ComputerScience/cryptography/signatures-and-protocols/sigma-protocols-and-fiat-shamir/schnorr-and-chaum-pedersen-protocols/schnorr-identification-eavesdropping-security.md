# Schnorr identification is secure against eavesdropping under discrete log

Let Schnorr identification use $k(n)\cdot n$-bit challenges with $2^{k(n) n} \le q$ and $2^{-k(n)n}$ negligible. Under the discrete-logarithm assumption it is secure against eavesdropping attacks: an adversary that first observes polynomially many honest transcripts and then interacts with the verifier impersonates the prover with negligible probability.

## Proof sketch

By honest-verifier zero knowledge, the eavesdropped transcripts can be simulated from the public key alone, so security against eavesdropping reduces to security against direct attacks, which reduces to discrete logarithms by rewinding.

## Depends on

- [Schnorr verifier's acceptance condition](../../schnorr-identification-scheme/accepts.md)
- [Discrete-logarithm experiment](../../../public-key/hardness-assumptions/dlog-game.md)

## Proof depends on

- [Schnorr identification is secure against direct attacks](../../zero-knowledge-and-arguments/schnorr-identification-is-secure-against-direct.md)
- [Linear Sigma protocols are complete, special sound and special HVZK](linear-sigma-protocols.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- C.-P. Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology 4(3), 1991.
