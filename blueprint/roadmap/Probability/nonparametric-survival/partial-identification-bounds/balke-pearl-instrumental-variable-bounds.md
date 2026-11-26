# Balke–Pearl bounds with a binary instrument

Let $Z$ (assignment), $S$ (treatment taken) and $Y$ (outcome) be binary, with potential outcomes $Y(z, s)$ and potential treatments $S(z)$. Assume independent assignment, $Z \perp \{S(0), S(1), Y(0,0), Y(0,1), Y(1,0), Y(1,1)\}$, and the exclusion restriction $Y(0, s) = Y(1, s)$ for $s = 0, 1$, so each unit has potential outcomes $Y(s)$ and the target is the average treatment effect $E[Y(1) - Y(0)]$. This effect is a linear combination of the probabilities of the joint law of the potential variables, and the observed probabilities $\Pr[Y = y, S = s \mid Z = z]$ are linear in the same probabilities; Balke and Pearl (1997) derived the sharp bounds on the effect under these assumptions by recognizing that their derivation is a linear programming problem, solved by the simplex algorithm, with a closed-form solution in terms of the observed probabilities (Richardson et al. 2014, Section 4.1). Balke and Pearl also showed that the earlier bounds of Robins (1989) for noncompliance are not tight (Gabriel, Sjölander and Sachs 2020). Being sharp under assumptions that imply those of any valid bounds, the Balke–Pearl bounds are never wider than the no-assumption bounds.

## Depends on

- [Exclusion restriction for an instrument](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/exclusion.md)
- [Independence assumption for an instrument](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/independence.md)

## Expansion

1. The model: response types for $S$ as a function of $Z$ and for $Y$ as a function of $S$, the independence and exclusion assumptions, and the linear map from type probabilities to observed laws.
2. The linear program and its dual; the vertex enumeration that gives the explicit bounds as maxima and minima of linear combinations of the eight observed probabilities.
3. Sharpness of the bounds.
4. Comparison with the [no-assumption bounds](../../../Probability/nonparametric-survival/partial-identification-bounds/manski-no-assumption-bounds-on-the-average-treatment-effect.md) and with the bounds of Robins, with an example where they differ.
5. Testable implications of the instrument assumptions, as a separate statement.

## Sources

- T. S. Richardson, M. G. Hudgens, P. B. Gilbert and J. P. Fine, Nonparametric bounds and sensitivity analysis of treatment effects, Statist. Sci. 29 (2014), 596–618, Section 4.1. <https://doi.org/10.1214/14-sts499>
- E. E. Gabriel, A. Sjölander and M. C. Sachs, Nonparametric bounds for causal effects in imperfect randomized experiments, 2020, Sections 1 and 2.3. <https://arxiv.org/abs/2010.05220>
- Original result: A. Balke and J. Pearl, Bounds on treatment effects from studies with imperfect compliance, J. Amer. Statist. Assoc. 92 (1997), 1171–1176. <https://doi.org/10.1080/01621459.1997.10474074> The linear-programming derivation and sharpness follow Richardson et al. (2014).
