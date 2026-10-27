---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.isGibonacciGood_iff
---

# Is Gibonacci Good iff

The congruence criterion for goodness: for `(a, b) ≠ (0, 0)` and
coprime `p, q`, the fraction `p / q` is good for `(a, b)` if and only
if `a ≡ -b p (q - p)⁻¹ ≡ -b q p⁻¹ (mod |q ^ 2 - p q - p ^ 2|)`. The
paper's modular inverses are written here with explicit inverse
witnesses `u` and `v`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FibonacciGeneratingFunctionsWanted](../../../../../sources/v2/WantedExt.md)
- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Lemma 6 (`jis-2024-24.3.1-lem-6`).
