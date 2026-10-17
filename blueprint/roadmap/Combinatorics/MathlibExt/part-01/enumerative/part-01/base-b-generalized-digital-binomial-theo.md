---
article_id: af_7154825b9643184c198f1b3f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.base_b_generalized_digital_binomial_theorem
---

# Base BGeneralized Digital Binomial

Base-`b` generalized digital binomial theorem.

The generalized binomial coefficients are rising factorials over
factorials; base-`b` digits are `n / b^i % b`, and the digital-dominance
sum is the `Finset.filter` over `m ≤ n`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Rising Factorial Binomial](../../../../../Algebra/MathlibExt/polynomial/asc-pochhammer-eval-add.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BaseBGeneralizedDigitalBinomial](../../../../../../sources/v2/MathlibExt.md)
- Hieu D. Nguyen, "A Generalization of the Digital Binomial Theorem," Journal of Integer Sequences 18 (2015), Article 15.5.7, Theorem (label th:digital-binomial-theorem-non-binary), equation (eq:digital-binomial-theorem-non-binary), lines 122–127, https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.tex
