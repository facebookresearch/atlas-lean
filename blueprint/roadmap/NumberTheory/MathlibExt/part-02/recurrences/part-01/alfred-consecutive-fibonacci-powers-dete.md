---
article_id: af_7d1ec25eb25e5227b1c7482f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.alfred_consecutive_fibonacci_powers_determinant
---

# Alfred Fibonacci Determinant

Alfred identity for consecutive Fibonacci powers: for integers `r`,
`s`, `k` with `r ≥ 0`, the `(r+1) × (r+1)` matrix with row `i` and
column `j` equal to `Int.fib (s + i * k) ^ (r - j) * Int.fib (s +
(i + 1) * k) ^ j` has determinant `(-1) ^ ((s + 1) * C(r+1,2) + k *
C(r+1,3)) * Int.fib k ^ C(r+1,2)` times the finite product over
`ℓ = 1, ..., r` of `Int.fib (k * ℓ) ^ (r + 1 - ℓ)`.

A slight variation of the result of Brother U. Alfred, "Some
determinants involving powers of Fibonacci numbers," Fibonacci
Quarterly 2 (1964), 81–92; the source's integer `r ≥ 0` is
rendered as `r : ℕ`, and `(-1)` to a possibly negative source
exponent via `Int.natAbs`.
Proves `Wanted` entry `alfred_consecutive_fibonacci_powers_determinant`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.AlfredFibonacciDeterminant](../../../../../../sources/v2/MathlibExt.md)
- Aram Tangboonduangjit and Thotsaporn Thanatipanonda, "Determinants Containing Powers of Generalized Fibonacci Numbers," Journal of Integer Sequences 19 (2016), Article 16.7.1, Corollary (label Alfred), lines 406–418, https://cs.uwaterloo.ca/journals/JIS/VOL19/Tangboonduangjit/aram5.tex
