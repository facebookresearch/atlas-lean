# CPA-secure ciphers rarely repeat ciphertexts

Let a symmetric cipher on $n$-bit messages be CPA secure. Then every efficient adversary with an encryption oracle obtains two equal ciphertexts (on any queries) only with negligible probability; concretely the repetition probability is at most $2\,\mathrm{CPAadv}(B)$ for a reduction $B$ of comparable cost, for all $n \ge 1$.

## Proof sketch

The reduction answers each query by submitting the pair (query, independent uniform message) and outputs $0$ iff a repetition occurs. Under bit $1$ repeated ciphertexts would decrypt to two independent uniform messages being equal, which is unlikely; under bit $0$ the repetition probability is the adversary's.

## Depends on

- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
