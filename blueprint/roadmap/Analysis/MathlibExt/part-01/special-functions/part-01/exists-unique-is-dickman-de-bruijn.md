---
article_id: af_30762a4f88c68619af71da9d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Real.existsUnique_isDickmanDeBruijn
---

# Dickman De Bruijn Exists Unique

There exists a unique total real function satisfying the Dickman–de Bruijn characterization.

## Depends on

- [Is Dickman De Bruijn](dickman-de-bruijn/is-dickman-de-bruijn.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique](../../../../../../sources/v2/MathlibExt.md)
- [O. Gorodetsky, *Rigidity of Averages over the Two Largest Prime Factors*](https://arxiv.org/abs/2608.05191), which characterizes the unique continuous function on the nonnegative reals and specifies its zero extension to negative inputs; Lean packages those clauses in `Real.IsDickmanDeBruijn`.
