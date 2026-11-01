---
article_id: af_d8e2ca161b0a798632b58802
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.james_reflexivity
---

# James reflexivity

For a Banach space over `ℝ` or `ℂ`, the canonical embedding into the bidual is surjective iff
every continuous linear functional attains its norm on the closed unit ball. Source:
R. C. James, Reflexivity and the Supremum of Linear Functionals, Ann. of Math. 66 (1957),
DOI 10.2307/1970122; Bourbaki form; Lean states `RCLike` Banach case with norm-attainment
equivalence for reflexivity.

Proof: The reverse implication uses the general real James convex-block argument, with Goldstine
approximation and weak-star cluster hulls. Restriction of scalars transfers the result to `RCLike`
fields.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Goldstine finite](goldstine-finite.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Normed.Module.JamesReflexivity](../../../../../../../sources/v2/MathlibExt.md)
