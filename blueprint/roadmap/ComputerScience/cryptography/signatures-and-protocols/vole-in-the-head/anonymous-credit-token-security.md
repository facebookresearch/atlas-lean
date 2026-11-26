# Credit conservation and unlinkability of VOLE-based anonymous credit tokens

(i) *Ledger conservation:* registering funding and accepting spends preserve the invariant that the total committed and refunded credit equals the total grant; every spend in a valid trace satisfies the balance equation and spend nullifier–context pairs are pairwise distinct, so the spent debit is at most the granted credit. (ii) *Extracted-model conservation:* if every redemption comes with an extracted certifying witness and the embedding of states into certification targets is injective on states in range, then any adversary making at most $q$ issuance queries violates credit conservation with probability at most the one-more (random-target) forgery advantage against the certification scheme with budget $q$; composing with straight-line VOLE-in-the-head extraction in the random oracle model gives a concrete query-bounded bound against unextracted adversaries. (iii) *Unlinkability:* if the commitment to the state is hiding and the spend proof is zero knowledge, a malicious issuer's view of spends is simulatable from the public amounts, provided the protocol aborts uniformly across branches; without this cross-branch non-abort guard an explicit adversary achieves unlinkability advantage $1$.

## Proof sketch

Conservation is an induction over the ledger trace, and a violation in the extracted model yields more valid certifications than issuance queries, i.e. a one-more forgery. Unlinkability: replace the commitments and proofs by simulated ones; a branch-dependent abort leaks the branch.

## Depends on

- [Anonymous credit tokens](anonymous-credit-tokens.md)

## Proof depends on

- [Straight-line extraction for VOLE-in-the-head in the random oracle model](vole-in-the-head-rom-extraction.md)
- [VOLE-based zero-knowledge proofs for arithmetic circuits](../vole-zero-knowledge/vole-circuit-zero-knowledge.md)

## Sources

- Tianyu Zhang, Christopher Patton and Samuel Schlesinger, "VOLE-ACT: anonymous credit tokens from VOLE-in-the-head" (design draft), 2026.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
