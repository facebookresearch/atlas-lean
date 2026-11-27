# 1CCA security implies multi-challenge CCA security

If a public-key scheme is 1CCA secure, it is secure in the batch multi-challenge CCA experiment with $Q$ challenges, with advantage at most $Q$ times a 1CCA advantage; this extends to fully adaptive interleaving of challenge and decryption queries.

## Proof sketch

Hybrid over the challenges: the reduction encrypts the non-planted challenges itself with the public key and remembers them, answering decryption queries on its own encryptions with the known plaintext and forwarding the others to its oracle.

## Depends on

- [1CCA security of public-key encryption](one-cca-security.md)

## Proof depends on

- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- M. Bellare, A. Boldyreva and S. Micali, "Public-Key Encryption in a Multi-user Setting: Security Proofs and Improvements", Advances in Cryptology – EUROCRYPT 2000, LNCS 1807, Springer, 2000, pp. 259–274, Theorem 1 (the case of one user).
