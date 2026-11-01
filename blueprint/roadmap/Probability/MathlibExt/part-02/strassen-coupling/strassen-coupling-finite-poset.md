---
article_id: af_83b68b8b5baf7bd5c87ef1b2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.StrassenCouplingWanted.strassen_coupling_finite_poset
---

# Strassen coupling finite poset

For nonnegative pmfs `p, q : α → ℝ` summing to 1, `p(U) ≤ q(U)` for every upward-closed `U` iff
there exists a nonnegative `π : α → α → ℝ` with row marginal `p`, column marginal `q`, and `π x y =
0` whenever `¬(x ≤ y)`.

## Depends on

- [Is Upper Set](is-upper-set.md)

## Proof depends on

- [Forall is Upper Set sum le iff exists coupling](forall-is-upper-set-sum-le-iff-exists-co.md)

## Sources

- [MathlibExt, MathlibExt.Probability.StrassenCoupling](../../../../../sources/v2/MathlibExt.md)
- V. Strassen, "The Existence of Probability Measures with Given Marginals", Ann. Math. Statist. 36 (1965), 423-439, DOI 10.1214/aoms/1177700153.
