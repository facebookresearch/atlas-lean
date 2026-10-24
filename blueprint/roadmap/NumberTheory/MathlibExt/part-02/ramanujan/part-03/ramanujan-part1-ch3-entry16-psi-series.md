---
article_id: af_3d9b3c54921b03d918db8889
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16PsiSeries.ramanujan_part1_ch3_entry16_psi_series
---

# Part1 Ch3 Entry16 Psi Series

`hu` selects the component of `{u | ‖u * exp (1 - u)‖ < 1}` containing `0` (given `h`,
    equivalent to `u.re < 1`); on the other component the series converges to a different
    value.

Proof: Entry 12 gives absolute and locally uniform convergence, and termwise
differentiation gives the recurrence in Berndt (16.4)-(16.5). The Jensen-series
base case from Berndt (16.6) extends to the star-convex domain by analytic uniqueness.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ramanujan part1 ch3 entry12 summable succ n general](../part-02/part1-ch3-entry12-summable-succ-n/ramanujan-part1-ch3-entry12-summable-suc.md)
- [Part1 Ch3 Entry16 Corollary1 Jensen Series](ramanujan-part1-ch3-entry16-corollary1-j.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry16PsiSeries](../../../../../../sources/v2/MathlibExt.md)
- Berndt, Ramanujan's Notebooks Part I, Chapter 3, construction and formulas (16.4)-(16.5), printed pp. 78-79 / PDF pp. 88-89.
