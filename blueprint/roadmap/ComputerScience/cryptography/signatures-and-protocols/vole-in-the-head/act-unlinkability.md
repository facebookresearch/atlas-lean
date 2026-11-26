# Malicious-issuer unlinkability of anonymous credit tokens

In a VOLE-based anonymous credit token scheme in which states are committed with a hiding commitment (every honest opening verifies) and spends are proved in zero knowledge, a malicious issuer interacting with honest holders in the finite query-bounded unlinkability game, where it must tell which of two holders with equal public spend amounts performed a spend, has advantage bounded by the commitment-hiding and zero-knowledge advantages of explicit reductions, provided the protocol's abort behaviour does not depend on the hidden branch. Without a cross-branch non-abort guard an explicit balance-partition adversary achieves advantage $1$ as soon as the balance bound is at least $3$: it issues balances that force one holder's spend to abort and not the other's.

## Proof sketch

Replace commitments and proofs by simulated ones in a hybrid argument; then the issuer's view is a function of public amounts only, except through aborts, which the guard equalizes.

## Depends on

- [Anonymous credit tokens](anonymous-credit-tokens.md)

## Proof depends on

- [VOLE-based zero-knowledge proofs for arithmetic circuits](../vole-zero-knowledge/vole-circuit-zero-knowledge.md)

## Sources

- Tianyu Zhang, Christopher Patton and Samuel Schlesinger, "VOLE-ACT: anonymous credit tokens from VOLE-in-the-head" (design draft), 2026.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
