---
article_id: af_45ac6f027dd04bf32fe957ae
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.KolmogorovMaximal.kolmogorov_maximal_inequality
---

# Kolmogorov Maximal

Finite discrete Kolmogorov maximal inequality: `n` independent variables with finite
state `α`, coordinate pmfs `p`,
`P[∃ i, |∑_{j ≤ i} X_j(ω_j)| ≥ lam] ≤ (∑_i E[X_i²]) / lam²`.

Primary source: A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter
unabhängiger Größen", Math. Ann. 99 (1928), 309–319, DOI 10.1007/BF01459098.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.KolmogorovMaximal](../../../../sources/v2/MathlibExt.md)
