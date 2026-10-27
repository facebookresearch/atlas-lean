---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted.erdos_straus_prime_restricted_representation_iff
---

# Erdos Straus Prime Structure Wanted

Chamberland's Theorem 1: for a prime `p`, a restricted
Erdős-Straus representation with `p ∤ a` and `p` dividing both `b` and
`c` exists if and only if `p = q * r - 4 * s₁ * s₂` for positive
`q r s₁ s₂` with `q ≡ 3 [MOD 4]` and both `s₁` and `s₂` dividing
`(q + 1) / 4`.

The equality on the right is written as
`p + 4 * s₁ * s₂ = q * r` over `ℕ` to avoid truncated subtraction.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ErdosStrausPrimeStructureWanted](../../../../sources/v2/WantedExt.md)
- Marc Chamberland, "The Erdős-Straus Conjecture and the Structure of Primes", Theorem 1.
