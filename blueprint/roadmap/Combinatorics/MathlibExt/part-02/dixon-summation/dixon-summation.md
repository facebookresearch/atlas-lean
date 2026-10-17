---
article_id: af_4aacf0ef17c1608c744cb2ff
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dixon_summation
---

# Dixon summation

Dixon's summation theorem for terminating 3F2 series (Proposition (Dixon)).

Proof: Wilf-Zeilberger pair. For `a, b ≥ 0` the normalized summand in `c = a₃` has the
certificate ratio `R(c, k) = -(a + k)(b + k) / (2(c - k + 1)(a + b + c + 1))`; induction on `c`
telescopes over the fixed window `[-a, a]`. Negative arguments make both sides zero.
Statement source: Abdesselam, arXiv:1903.11147v2, Proposition (Dixon), TeX lines 502-512.

## Depends on

- [Ext Fact](ext-fact.md)
- [Inv Fact](inv-fact.md)
- [Upsilon₃](upsilon.md)

## Proof depends on

- [Dixon Bound](dixon-bound.md)
- [Dixon Summand](dixon-summand.md)
- [Ext Fact of neg](ext-fact-of-neg.md)
- [Int Binom](int-binom.md)
- [Inv Fact of neg](inv-fact-of-neg.md)
- [Inv Fact shift](inv-fact-shift.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.DixonSummation](../../../../../sources/v2/MathlibExt.md)
