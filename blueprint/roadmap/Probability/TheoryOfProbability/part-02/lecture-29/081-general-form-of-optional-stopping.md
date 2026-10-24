---
article_id: af_bdd1d2ddf1f724c32983f9b3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: general_optional_stopping_bounded
---

# Theorem (General form of optional stopping)

If $L \leq M$ are stopping times and $Y_{M \wedge n}$ is a uniformly integrable submartingale, then $E[Y_L] \leq E[Y_M]$ and $Y_L \leq E(Y_M \mid \mathcal{F}_L)$.

## Depends on

- [Definition (Stopping time)](../../part-01/lecture-23/051-stopping-time.md)
- [Definition (Conditional expectation)](../../part-01/lecture-25/053-conditional-expectation.md)
- [Definition (Uniform integrability)](../../part-01/lecture-28/066-uniform-integrability.md)
- [Definition (Martingale, supermartingale, submartingale)](091-martingale-supermartingale-submartingale.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 29, General optional stopping theorem section](../../../../../sources/v1/TheoryOfProbability.md)
