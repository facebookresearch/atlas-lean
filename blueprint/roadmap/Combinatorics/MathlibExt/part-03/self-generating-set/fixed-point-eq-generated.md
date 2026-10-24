---
article_id: af_df449e92a6bbfb610dabcbcb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.SelfGeneratingSet.fixedPoint_eq_generated
---

# Fixed Point eq generated

Under strict growth, a fixed point is the generated closure. The proof uses strong induction:
if a non-seed element is `f x`, then strict growth gives `x < f x`.

## Depends on

- [Fixed Point](fixed-point.md)
- [Generated Set](generated-set.md)
- [Strict Growth](strict-growth.md)

## Proof depends on

- [Gen](gen.md)
- [SG](sg.md)
- [Fixed Point is SG](fixed-point-is-sg.md)
- [Generated le of sg](generated-le-of-sg.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SelfGeneratingSet](../../../../../sources/v2/MathlibExt.md)
