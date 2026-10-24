---
article_id: af_8e66d115a16223e61ac0ee13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.Statistics.NeymanPearson.neyman_pearson_dominated_two_simple
---

# Neyman Pearson

Dominated Neyman–Pearson lemma (two simple hypotheses), strengthened form.

For `k ≥ 0`, a test `φ⋆` taking the value `1` where `q > k * p` and `0` where
`q < k * p` is most powerful among tests with no larger `p`-size. No normalization
of `p` or `q` and no tie-breaking condition on `{q = k * p}` are assumed.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.Statistics.NeymanPearson](../../../../../sources/v2/MathlibExt.md)
- J. Neyman and E. S. Pearson, "On the problem of the most efficient tests of statistical hypotheses", Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337, DOI `10.1098/rsta.1933.0009`.
