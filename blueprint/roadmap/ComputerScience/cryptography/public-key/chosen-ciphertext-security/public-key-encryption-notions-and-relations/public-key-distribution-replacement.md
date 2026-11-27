# Replacing the public-key distribution in chosen-message security

Let two public-key distributions $\mathcal{P}_0, \mathcal{P}_1$ (for example honest keys and lossy or simulated keys) be computationally indistinguishable. Then the CPA advantage of any adversary against keys from $\mathcal{P}_0$ and from $\mathcal{P}_1$ differ by at most twice the key-distinguishing advantage of a reduction that runs the adversary on the challenge key and encrypts the challenge itself.

## Proof sketch

The reduction samples the challenge bit, runs the CPA experiment on the given public key, and outputs whether the adversary guessed correctly.

## Depends on

- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
