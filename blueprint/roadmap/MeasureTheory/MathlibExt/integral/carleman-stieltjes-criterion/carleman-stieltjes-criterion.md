---
article_id: af_701ed5db99bc6e41c0ee98e6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.carleman_stieltjes_criterion
---

# Carleman stieltjes criterion

Carleman Stieltjes criterion: divergence of the all-moment series implies
    determinacy on [0, infinity) (Lin Theorem 2, (s6) implies (s7)).
    Corpus `jis_grounded_5e39d97b31ef58deb38a5a58`. Condition (s6) is the
    series sum_{k = 1} m_k^(-1 / (2 * k)) diverging, with m_k given by
    `ProbabilityTheory.moment id k mu`; condition (s7) is moment determinacy
    on [0, infinity). Source spans: definition lines 57-75, criterion lines
    297-321, TeX SHA-256 e2dcb54a4b25d57ae3ad6e52267862aeca0ae2f38ffb729df0d727013d3c3080;
    JIS application lines 152-177, source SHA-256
    66f0a4a264af03f82a43e3b37e62cc80cf0aed6f43e476e56456006203232bd0.

Proof: Symmetrize through the square-root map, apply Denjoy--Carleman quasi-analytic
uniqueness to the difference of characteristic functions, then push forward by squaring.

## Depends on

- [Stieltjes Moment Determinate](stieltjes-moment-determinate.md)

## Proof depends on

- [Summable geometric means](summable-geometric-means.md)

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.Integral.CarlemanStieltjesCriterion](../../../../../sources/v2/MathlibExt.md)
