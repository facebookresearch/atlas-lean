# CPA-secure ciphers rarely repeat ciphertexts

Let a symmetric cipher on $n$-bit messages, with $n$ a function of the security parameter such that $2^{-n}$ is negligible, be CPA secure. Then every efficient adversary with an encryption oracle obtains two equal ciphertexts (on any queries) only with negligible probability; concretely, for an adversary making $Q$ queries, the repetition probability is at most $\mathrm{CPAadv}(B) + \binom{Q}{2}/2^n$ for a reduction $B$ whose running time exceeds that of the adversary by at most the time of sampling $Q$ uniform $n$-bit messages and checking $Q$ ciphertexts for a repetition.

## Proof sketch

The reduction answers each query by submitting the pair (query, independent uniform message) and outputs $0$ iff a repetition occurs. Under bit $1$ repeated ciphertexts would decrypt to two independent uniform messages being equal, which is unlikely; under bit $0$ the repetition probability is the adversary's.

## Depends on

- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
