# Schnorr's protocol is a proof of knowledge of discrete logarithms

For Schnorr's protocol over a prime-order group family, there is a rewinding knowledge extractor that, given oracle access to any prover that convinces the verifier on statement $u$ with probability $\varepsilon$ over challenges from a set of size $N$, outputs $\log_g u$ with probability at least $\varepsilon^2 - \varepsilon/N$ in expected polynomial time.

## Proof sketch

Run the prover, rewind it to the commitment, and answer a second, independent challenge; by the rewinding (forking) lemma both runs accept with distinct challenges with probability at least $\varepsilon^2 - \varepsilon/N$, and special soundness extracts the discrete logarithm.

## Depends on

- [The Schnorr identification protocol as a Sigma protocol](../../zero-knowledge-proofs/schnorr-sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)

## Proof depends on

- [The rewinding lemma](../../zero-knowledge-and-arguments/the-rewinding-lemma.md)
- [The general forking lemma](../random-oracle-signatures/general-forking-lemma.md)

## Sources

- C.-P. Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology 4(3), 1991.
- M. Bellare and O. Goldreich, "On Defining Proofs of Knowledge", Advances in Cryptology (CRYPTO 1992), LNCS 740, 1993.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
