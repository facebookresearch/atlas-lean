---
article_id: af_4c81b45a63d256672c89bed8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.prime_power_factorization_sum_eq_iff
---

# Prime Power Factorization Sum

A prime power `y = p ^ m` is fixed by the sum of the `s`-th powers of its prime
factors, counted with multiplicity, exactly when `m = p ^ k` and
`s = p ^ k - k` for some natural number `k`.

`y.factorization.sum fun q e => e * q ^ s` is the paper's `T_s(y)`; for
`y = p ^ m` this is `m * p ^ s`, and `m * p ^ s = p ^ m` forces `m` to be a
power of `p`.
Proves `Wanted` entry `prime_power_factorization_sum_eq_iff`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimePowerFactorizationSum](../../../../sources/v2/MathlibExt.md)
- Spencer P. Hurd and Judson S. McCranie, "Integers That Are Sums of Uniform Powers of All Their Prime Factors: The Sequence A068916," Journal of Integer Sequences 22 (2019), Article 19.3.4, Theorem 1 (label origThm1), lines 187–189, https://cs.uwaterloo.ca/journals/JIS/VOL22/Hurd/hurd1.tex
