---
article_id: af_5846b9e3b3a010ce4d332ca7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fuss_catalan_dvd_choose
---

# Fuss Catalan Divisibility

Classical case: for `a ≥ 2` and `n ≥ 1`, `(a-1)*n+1` divides `C(a*n, n)`,
so the Fuss-Catalan numbers are integers.

The `r = 1` case of eq:FC is `C(a*n,n)/((a-1)*n+1)`; the source proves
integrality for the Lucasnomial family (Theorem thm:1) while the classical
divisibility is cited as known. Verified computationally for `2 ≤ a ≤ 9`
and `1 ≤ n ≤ 39`.
Proves `Wanted` entry `fuss_catalan_dvd_choose`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FussCatalanDivisibility](../../../../../../sources/v2/MathlibExt.md)
- Christian Ballot, "Lucasnomial Fuss-Catalan Numbers and Related Divisibility Questions," Journal of Integer Sequences 21 (2018), Article 18.6.5, equation (label eq:FC), lines 115–117 (classical definition), line 127 (classical integrality recorded as known), Theorem (label thm:1), lines 516–521 (Lucasnomial generalization), https://cs.uwaterloo.ca/journals/JIS/VOL21/Ballot/ballot30.tex
