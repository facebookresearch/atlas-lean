# Prefix union bound for round-by-round sound IOPs

Let a public-coin IOP be run against an arbitrary (randomized, adaptive) prover. If the empty transcript is doomed, every good step preserves doomedness, and in round $j$ the probability over the challenge of escaping is at most $\varepsilon_j$ whatever the prefix, then the probability that the final transcript is not doomed after $k$ rounds is at most $\sum_{j<k}\varepsilon_j$. In particular the probability that the verifier accepts a false statement is at most $\sum_{j<k}\varepsilon_j + \varepsilon_{\mathrm{query}}$, the sum of the commit-phase escape probabilities and the final query error.

## Proof sketch

Union bound over the first round in which the doomed invariant fails; at that round the escape probability is bounded conditionally on the prefix.

## Depends on

- [Public-coin interactive oracle proofs](public-coin-iop.md)

## Sources

- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
