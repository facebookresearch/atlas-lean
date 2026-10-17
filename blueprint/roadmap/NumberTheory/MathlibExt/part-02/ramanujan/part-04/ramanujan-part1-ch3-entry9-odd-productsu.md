---
article_id: af_3bc6e971183a1fe79b50f477
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9OddProductsummable.ramanujan_part1_ch3_entry9_odd_productsummable
---

# Part1 Ch3 Entry9 Odd Productsummable

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 9(i), definitions printed
    p. 53 / PDF p. 63 and result printed p. 54 / PDF p. 64.
It follows from `Complex.summable_neg_pow_mul_pow_div_prod_add_mul`: the upper sector bound keeps
`(z + a) / b` off the negative real axis, so no factor of the denominator vanishes. The hypothesis
`hεlt`, the radius (taken to be `0`) and the lower sector bound are unused and keep the source's
shape.
Proves `Wanted` entry `ramanujan_part1_ch3_entry9_odd_productsummable`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Rising Product Series](../../../../../Analysis/MathlibExt/part-01/specific-limits/summable-neg-pow-mul-pow-div-prod-add-mu.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9OddProductsummable](../../../../../../sources/v2/MathlibExt.md)
