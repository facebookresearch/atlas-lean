# Chosen-ciphertext security implies chosen-plaintext security

Every 1CCA-secure (in particular every CCA-secure) public-key scheme is semantically secure: a CPA adversary is a CCA adversary that makes no decryption queries, with identical advantage.

## Proof sketch

The CPA experiment is the CCA experiment restricted to adversaries that never query the decryption oracle.

## Depends on

- [1CCA security of public-key encryption](one-cca-security.md)
- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Sources

- M. Bellare, A. Desai, D. Pointcheval and P. Rogaway, "Relations among Notions of Security for Public-Key Encryption Schemes", Advances in Cryptology – CRYPTO '98, LNCS 1462, Springer, 1998, pp. 26–45.
- M. Bellare, A. Boldyreva and S. Micali, "Public-Key Encryption in a Multi-user Setting: Security Proofs and Improvements", Advances in Cryptology – EUROCRYPT 2000, LNCS 1807, Springer, 2000, pp. 259–274, Remark 1.
