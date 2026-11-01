---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.isGibonacciGood_ratios_infinite_iff
---

# Is Gibonacci Good ratios infinite iff

For coprime `p, q`, let `H` be the Gibonacci sequence with
`H_0 = p` and `H_1 = q`. Then infinitely many pairs `(a, b)` make
every ratio `H_n / H_{n+1}` (with nonzero denominator) good, and this
holds for a given `(a, b)` if and only if
`a ≡ -b p (q - p)⁻¹ ≡ -b q p⁻¹ (mod |q ^ 2 - p q - p ^ 2|)`, with the
modular inverses written via explicit witnesses. The paper indexes
`H` by all integers; this statement covers `n ∈ ℕ`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FibonacciGeneratingFunctionsWanted](../../../../../sources/v2/WantedExt.md)
- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Theorem 3 (`jis-2024-24.3.1-thm-3`).
