---
article_id: af_049f8170a72a656e1df52f85
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry13CorollarySchroder.ramanujan_part1_ch3_entry13_corollary_schroder
---

# Ramanujan part1 ch3 entry13 corollary schroder

`{w | ‖w‖ ≤ ‖exp (w - 1)‖}` has a bounded lobe containing `0` and an unbounded lobe, meeting
    only at `w = 1`. `hw1` selects the bounded lobe (given `hw`, it is equivalent to `w.re ≤ 1`);
    on the unbounded lobe the identity fails in general.

Proof: Following Berndt's formula (13.8), we use Abel's binomial identity, a Cauchy product and a
holomorphic ODE; radial continuity selects the unit-disk branch of `u ↦ u * exp (-u)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry13CorollarySchroder](../../../../../../../sources/v2/MathlibExt.md)
- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Corollary to Entry 13, formula (13.8), printed p. 70 / PDF p. 80.
