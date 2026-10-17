---
article_id: af_81933f8ccbe25d068c27082e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.arbitrarily_long_arithmetic_progressions_of_powerful_numbers
---

# Arbitrarily long arithmetic progressions of powerful numbers

For every length at least three, there is a nonconstant arithmetic progression of positive
powerful numbers.

Provenance: Tsz Ho Chan, "Arithmetic Progressions Among Powerful Numbers",
Journal of Integer Sequences 26 (2023), Article 23.1.1, Theorem `thm-longAP`,
source lines 97–99,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Chan/chan33.tex>.
The paper notes the result is not new (see remark 2 in [H] there) and includes a
proof for completeness. Powerful (squarefull) means every prime divisor appears
with exponent at least two; nonconstant is `0 < d`.
It follows from `arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general`, which
states powerfulness as `Nat.IsKFull 2`; the hypothesis `hk` is unused and keeps the source's
shape.
Proves `Wanted` entry `arbitrarily_long_arithmetic_progressions_of_powerful_numbers`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Arbitrarily long arithmetic progressions of powerful numbers general](arbitrarily-long-arithmetic-progressions.md)
- [Is KFull](../../part-07/kfull/is-kfull.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PowerfulNumbersArithmeticProgressions](../../../../../sources/v2/MathlibExt.md)
