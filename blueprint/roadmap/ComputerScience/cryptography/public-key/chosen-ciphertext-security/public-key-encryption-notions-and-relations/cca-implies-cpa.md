# Chosen-ciphertext security implies chosen-plaintext security

Every 1CCA-secure (in particular every CCA-secure) public-key scheme is semantically secure: a CPA adversary is a CCA adversary that makes no decryption queries, with identical advantage.

## Proof sketch

The CPA experiment is the CCA experiment restricted to adversaries that never query the decryption oracle.

## Depends on

- [1CCA security of public-key encryption](one-cca-security.md)
- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
