---
article_id: af_7f742003e5f4a13ab8f542b9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalized_pell_eq_two_colored_compositions
---

# Generalized Pell Numbers

The number of compositions of `n` with parts at most `k`, where a part of size one has two
colors, equals the `(n + 1)`-st generalized Pell number. Symbols `0` and `1` encode the two
colors of part one, while symbol `i` encodes the uncolored part `i` for `2 ≤ i ≤ k`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GeneralizedPellNumbers](../../../../../../sources/v2/MathlibExt.md)
- Jhon J. Bravo, Jose L. Herrera, and José L. Ramírez, "Combinatorial Interpretation of Generalized Pell Numbers," Journal of Integer Sequences 23 (2020), Article 20.2.1, theorem `C_k(n) = P_{n+1}^{(k)}` for `n ≥ 1` (equation label Equation1), lines 441–447, https://cs.uwaterloo.ca/journals/JIS/VOL23/Bravo/bravo4.tex. Proves `Wanted` entry `generalized_pell_eq_two_colored_compositions`.
