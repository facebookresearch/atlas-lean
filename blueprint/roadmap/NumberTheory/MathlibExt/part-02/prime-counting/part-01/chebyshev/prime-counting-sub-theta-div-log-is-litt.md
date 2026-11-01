---
article_id: af_499dc8c312b2abbeaf1b7f9e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Chebyshev.primeCounting_sub_theta_div_log_isLittleO
---

# Prime Counting sub theta div log is Little O

The error `π(x) - θ(x) / log x` is little-o of `x / log x`.

This upgrades `Chebyshev.primeCounting_sub_theta_div_log_isBigO`, using that
`x / log x ^ 2` is little-o of `x / log x`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.Chebyshev](../../../../../../../sources/v2/MathlibExt.md)
