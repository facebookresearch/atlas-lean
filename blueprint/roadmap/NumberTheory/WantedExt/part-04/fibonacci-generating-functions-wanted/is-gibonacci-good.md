---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsGibonacciGood
---

# Is Gibonacci Good

The rational `x` is good for `(a, b)`: the generating function is
defined at `x` (its denominator does not vanish) and takes an integer
value there.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gibonacci Generating Value](gibonacci-generating-value.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.FibonacciGeneratingFunctionsWanted](../../../../../sources/v2/WantedExt.md)
- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1 (the paper says `x = p / q` is good for `(a, b)` when `G^{(a,b)}(x)` is an integer; Theorem 1 uses the same integrality without the word good).
