---
article_id: af_99db03a484a316376b8ca1df
declaration: theorem
origin: cited
lean: MeasureTheory.doob_sq_maximal_ineq_iSup
---

# Theorem (Square integrable martingale maximal inequality)

If $X_n$ is a martingale with $E[X_n^2] < \infty$ for all $n$, and $A_n = \sum_{m=1}^n E[(X_m - X_{m-1})^2 \mid \mathcal{F}_{m-1}]$, then $E[\sup_m |X_m|^2] \leq 4 E[A_\infty]$.

## Depends on

- [Definition (Conditional expectation)](../lecture-25/053-conditional-expectation.md)
- [Theorem (Doob's decomposition)](../../part-02/lecture-27/064-doob-s-decomposition.md)
- [Definition (Martingale, supermartingale, submartingale)](../../part-02/lecture-29/091-martingale-supermartingale-submartingale.md)

## Proof depends on

- [Monotone convergence](../lecture-5/011-monotone-convergence.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 28](../../../../../sources/v1/TheoryOfProbability.md)
