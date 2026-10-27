---
article_id: af_1bb6816924c858f2edcf4037
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.Statistics.GlivenkoCantelliWanted.glivenko_cantelli
---

# Glivenko cantelli

If `X : ℕ → Ω → ℝ` is i.i.d. on a probability space, then almost surely the empirical CDF
`(empiricalCount X n ω x : ℝ)/(n+1)` converges uniformly in `x : ℝ` to `(P (X 0 ⁻¹' Iic
x)).toReal`. Source: V. Glivenko, Sulla determinazione empirica delle leggi di probabilita, Giorn.
Ist. Ital. Attuari 4 (1933) 92–99; F. Cantelli 1933; textbook in Durrett, Probability Theory and
Examples, 5th ed., Probability and Measure

## Depends on

- [Empirical Count](empirical-count.md)

## Sources

- [MathlibExt, MathlibExt.Probability.Statistics.GlivenkoCantelli](../../../../../../sources/v2/MathlibExt.md)
