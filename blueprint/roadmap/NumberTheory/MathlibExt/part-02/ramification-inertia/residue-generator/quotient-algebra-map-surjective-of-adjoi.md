---
article_id: af_bd40e4d971cd4cf6b5258d3c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top
---

# Quotient algebra Map surjective of adjoin singleton eq top

If `B` is generated over `A` by an element `π ∈ q`, then the canonical
`A`-algebra map `A ⧸ q.comap (algebraMap A B) → B ⧸ q` is surjective.

Indeed, lift a class to `b : B`, write `b` as `Polynomial.aeval π p`, and use
the constant coefficient `p.coeff 0`: all higher terms vanish in `B ⧸ q`
because `π` maps to zero.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.RamificationInertia.ResidueGenerator](../../../../../../sources/v2/MathlibExt.md)
