---
article_id: af_c527eb629232399591c6bf0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.QRWhitney.whitneySecond_eq_sum_qStirlingSecond
---

# Whitney Second eq sum q Stirling Second

Closed form of the `(q, r)`-Whitney numbers of the second kind through any family
`qStirlingSecond` with the recurrence of the `q`-Stirling numbers of the second kind:
`W(a, k) = ∑ j, C(a, j) * r ^ (a - j) * m ^ (j - k) * qStirlingSecond j k`.

## Depends on

- [Q Brack](../qrwhitney-numbers/q-brack.md)
- [Whitney Second](../qrwhitney-numbers/whitney-second.md)

## Proof depends on

- [Whitney Second succ succ](../qrwhitney-numbers/whitney-second-succ-succ.md)
- [Whitney Second succ zero](../qrwhitney-numbers/whitney-second-succ-zero.md)
- [Whitney Second zero succ](../qrwhitney-numbers/whitney-second-zero-succ.md)
- [Whitney Second zero zero](../qrwhitney-numbers/whitney-second-zero-zero.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.QRDowlingQStirlingExpansion](../../../../../../../sources/v2/MathlibExt.md)
