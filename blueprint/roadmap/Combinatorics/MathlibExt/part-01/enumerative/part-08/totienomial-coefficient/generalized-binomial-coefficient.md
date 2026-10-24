---
article_id: af_0f6d4756308f22205959dcd2
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.generalizedBinomialCoefficient
---

# Generalized Binomial Coefficient

Totalized generalized binomial coefficient.  On the source domain, where `f i > 0`
for every positive `i`, this is the source's exact quotient.  For arbitrary Nat-valued `f`,
Lean's rational division convention extends the definition by returning zero when the
denominator is zero.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Factorial](generalized-factorial.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient](../../../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex
