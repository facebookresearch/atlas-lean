---
article_id: af_8b166036a03099fc8c058ef7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gamma_closed_form
---

# Gamma Closed Form

Closed form for the Eloe-Kublik gamma array: any doubly indexed real sequence
satisfying the linear recursion with the given initial and vanishing
conditions has `γ n k = (-1/4)^k * choose n (2*k) * catalan k`.

The `k ≤ n / 2` bound is the paper's `0 ≤ k ≤ ⌊n/2⌋`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GammaClosedForm](../../../../../../sources/v2/MathlibExt.md)
- Paul Eloe and Catherine Kublik, "When Numerical Analysis Crosses Paths with Catalan and Generalized Motzkin Numbers," Journal of Integer Sequences 21 (2018), Article 18.8.4, Theorem `closedform_thm`, lines 390-396, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Kublik/kublik2.tex>; the recursion and initial conditions are equation `gamma_linear_recursion`, lines 87-91.
