---
article_id: af_a497f638ff0739a47f53de77
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoulliasymptotic.ramanujan_part1_ch7_entry14_bernoulliasymptotic
---

# Part1 Ch7 Entry14 Bernoulliasymptotic

Proof outline: the limits `c k` are the Stieltjes constants. For
`ζ(s) - 1/(s-1)`, the `k`th derivative at `s = 1` is `(-1)^k c k`, while the
normalized Taylor coefficient is `(-1)^k c k / k! = chapter7StieltjesA c k`.
The identity follows by termwise differentiation in `s` and evaluation at `s = 1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Part1 Ch7 Entry13 Bernoullirecurrence](ramanujan-part1-ch7-entry13-bernoullirec.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic](../../../../../../sources/v2/MathlibExt.md)
- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
