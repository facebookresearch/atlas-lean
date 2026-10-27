---
article_id: af_b44afaa52a93701570f7bef4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15Example1ExponentialSeries.ramanujan_part1_ch3_entry15_example1_exponential_series
---

# Part1 Ch3 Entry15 Example1 Exponential Series

Proof: Following Berndt and the generalized binomial series of Graham, Knuth, and Patashnik,
the series is realized as `B_n(z) ^ m` with `B_n = 1 + z * B_n ^ n`; root selection at
`z = 2 ^ (-n)`, with the endpoint supplied by Entry 14's Catalan-power series, gives `B_n = 2`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Part1 Ch3 Entry14 Cor1 Catalanpowerseries](ramanujan-part1-ch3-entry14-cor1-catalan.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry15Example1ExponentialSeries](../../../../../../sources/v2/MathlibExt.md)
- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 15, Example 1, printed pp. 73-75 / PDF pp. 83-85.
