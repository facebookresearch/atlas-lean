# Multi-target and one-more preimage games

Let $f_{pk}$ be a (many-to-one) trapdoor function with preimage sampler $\mathrm{Inv}_{sk}$, viewed as a signature scheme whose messages are targets and whose signatures are preimages. In the *$N$-target game* the challenger draws $N$ uniform targets $y_1, \dots, y_N$ and the adversary wins if it outputs a preimage of one of them. In the *one-more preimage game* with budget $b$ the adversary may additionally request preimages of up to $b$ targets of its choice and wins if it outputs valid preimages for at least $b + 1$ distinct target slots. The game is unwinnable when $N \le b$, and with zero preimage requests it contains the ordinary multi-target game without loss. These games underlie the security of hash-and-sign signatures and of anonymous-token issuance.

## Depends on

- [Trapdoor permutations](../../../public-key/hardness-assumptions/trapdoor-permutations.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
