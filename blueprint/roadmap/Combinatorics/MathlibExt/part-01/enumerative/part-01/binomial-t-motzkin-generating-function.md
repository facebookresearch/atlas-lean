---
article_id: af_f779ad66d1062db1715f32e1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.binomial_tMotzkin_generatingFunction
---

# Binomial TMotzkin Paths

The generating function counting binomial `[t]`-Motzkin paths by length is the
`t`-th power of the generalized Catalan generating function. Steps are
`Σ k : Fin (t+1), Fin (t.choose k)` with height change `1 - k`, so there are
`C(t,k)` colors of the step of height change `1 - k`; `catalanGF` is the source
`C_t(z) = ∑ C(tn,n) / ((t-1)n+1) z^n` (source line 321).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BinomialTMotzkinPaths](../../../../../../sources/v2/MathlibExt.md)
- Naiomi T. Cameron and Jillian E. McLeod, "Returns and Hills on Generalized Dyck Paths," Journal of Integer Sequences 19 (2016), Article 16.6.1, Theorem (binomial `[t]`-Motzkin generating function), lines 987–989, https://cs.uwaterloo.ca/journals/JIS/VOL19/McLeod/mcleod3.tex
