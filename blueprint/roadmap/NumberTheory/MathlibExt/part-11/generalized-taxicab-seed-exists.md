---
article_id: af_ca419c2e85bc89cb0b2672ba
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalized_taxicab_seed_exists
---

# Taxicab Seed

For fixed `m` and `t`, `T n m t` is `some v` exactly when `v` is the least number
expressible as a sum of exactly `n` positive `m`-th powers in at least `t`
distinct unordered `Multiset ℕ` ways, and `T n m t` is `none` when no qualifying
value exists; a seed `s₀` is a smallest positive integer from which every defined
value grows affinely with slope one.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.TaxicabSeed](../../../../sources/v2/MathlibExt.md)
- Jeffrey H. Dinitz, Richard A. Games, and Robert L. Roth, “Seeds for Generalized Taxicab Numbers”, Journal of Integer Sequences 22 (2019), Article 19.3.3, Theorem line 229, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Dinitz/dinitz8.tex>. Proves `Wanted` entry `generalized_taxicab_seed_exists`.
