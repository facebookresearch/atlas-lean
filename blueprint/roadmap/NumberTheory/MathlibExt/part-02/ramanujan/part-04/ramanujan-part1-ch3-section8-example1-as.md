---
article_id: af_ebd79190ea8fc090d05a260e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example1Asymptotic.ramanujan_part1_ch3_section8_example1_asymptotic
---

# Part1 Ch3 Section8 Example1 Asymptotic

For `lam = ⊥` the expansion is stated on the sector `|arg z| ≤ π / 2 - eps`, as for finite
    `lam`; on the wider sector `|arg z| ≤ π - eps` it fails, e.g. for `a j = j! (-2/3)^j`.

Proof: Use convergence at one real point to obtain absolute convergence two units to the right,
then expand each `1 / ((z + 1)⋯(z + j + 1))` termwise in powers of `1 / z` and bound the tail.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Section8Example1Asymptotic](../../../../../../sources/v2/MathlibExt.md)
- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 1, formula (8.1), printed p. 50 / PDF p. 60.
