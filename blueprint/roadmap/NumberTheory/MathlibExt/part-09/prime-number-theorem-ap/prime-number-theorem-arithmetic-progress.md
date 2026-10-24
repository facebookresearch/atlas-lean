---
article_id: af_9feade00b0f50dcd9d595a56
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeNumberTheoremAPWanted.prime_number_theorem_arithmetic_progression
---

# Prime number theorem arithmetic progression

For `q ≥ 2` and `Nat.Coprime a q`, the count of primes `p ≤ n` with `p ≡ a [MOD q]` satisfies
`count * log n / n → 1 / φ(q)` as `n → ∞`, where `φ = Nat.totient`. Source: G. L. Dirichlet 1837
existence, PNT for AP by de la Vallée Poussin and Hadamard 1896-1899 extensions; textbook in
Montgomery-Vaughan, Multiplicative Number Theory I, Multiplicative Number Theory

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime Counting sub theta div log is Little O](../../part-02/prime-counting/part-01/chebyshev/prime-counting-sub-theta-div-log-is-litt.md)
- [Psi Residue Class](../../part-02/prime-counting/part-02/residue-class-psi/psi-residue-class.md)
- [Tendsto psi Residue Class div self](../../part-02/prime-counting/part-02/weak-pntarithmetic-progression/tendsto-psi-residue-class-div-self.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeNumberTheoremAP](../../../../../sources/v2/MathlibExt.md)
