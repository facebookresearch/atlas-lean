---
article_id: af_9ce4b2bcb413e85de7cfc8ee
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.poly_initial_expansion
---

# Poly initial expansion

Proposition 5 expansion of the associated polynomial at index zero by
weighted Stirling numbers of the second kind: the binomial-weighted sum of
`a 0 (n - k)` against `x ^ k` equals the signed factorial-weighted sum of the
canonical generalized Stirling numbers against `a m 0`, for arrays satisfying the
stated recurrence in the second argument.

Proof: Following Dil, Kurt, and Cenkci, Proposition 5, the proof is induction on
`t` for Chen's expansion `chen_stirlingSecond_expansion`, followed by a binomial convolution.

## Depends on

- [Generalized Stirling Second](../../part-04/generalized-stirling-numbers/generalized-stirling-second.md)

## Proof depends on

- [Chen stirling Second expansion](chen-stirling-second-expansion.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PolyInitialExpansion](../../../../../../../sources/v2/MathlibExt.md)
- Ayhan Dil, Veli Kurt, and Mehmet Cenkci, "Algorithms for Bernoulli and Related Polynomials," Journal of Integer Sequences 10 (2007), Article 07.5.4, Proposition 5 (label prop5), lines 661–671, https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex
