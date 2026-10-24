---
article_id: af_16fe3026c26f5eb6c8170c17
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.compositions_parts_one_two_three_eq_tribonacci
---

# Compositions parts one two three eq tribonacci

The number of compositions of a positive integer using only the parts
`1`, `2`, and `3` is the corresponding Tribonacci number.

The result is due to V. E. Hoggatt, Jr., and M. Bicknell,
"Palindromic compositions," Fibonacci Quarterly 13 (1975), 350–356,
cited as [V] at source lines 429–430.

Proof: Split each nonempty composition by its first part, sum the resulting recurrence over its
length, and use strong induction, following Stanley, Section 1.2, and OEIS A000073.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CompositionsTribonacci](../../../../../../../sources/v2/MathlibExt.md)
- Yu-hong Guo, "Some Identities For Palindromic Compositions," Journal of Integer Sequences 21 (2018), Article 18.6.6, Theorem citing [V], lines 118–125, https://cs.uwaterloo.ca/journals/JIS/VOL21/Guo/guo19.tex
