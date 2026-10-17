---
article_id: af_2cee1d5623d6d25acf3a0f03
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.falling_equiv
---

# Falling Binomial Transform

The `k`-fold binomial transform equals the falling `k`-binomial transform: iterating the
binomial transform `k` times for nonnegative `k : ℤ`, and iterating the inverse binomial
transform `-k` times for negative `k`, gives the falling `k`-binomial transform as whole
integer sequences. Source: Michael Z. Spivey and Laura L. Steil, "The k-Binomial Transforms and
the Hankel Transform", Journal of Integer Sequences 9 (2006), Article 06.1.1, Theorem
`falling_equiv`, lines 636-640,
<https://cs.uwaterloo.ca/journals/JIS/VOL9/Spivey/spivey7.tex>.

## Depends on

- [Falling KBinomial Transform](falling-kbinomial-transform/falling-kbinomial-transform.md)
- [Multiple Binomial Transform](../part-05/multiple-binomial-transform.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FallingBinomialTransform](../../../../../../sources/v2/MathlibExt.md)
