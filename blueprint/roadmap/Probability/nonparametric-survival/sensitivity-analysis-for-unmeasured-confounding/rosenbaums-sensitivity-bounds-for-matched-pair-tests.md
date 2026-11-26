# Rosenbaum's sensitivity bounds for matched-pair signed score tests with general scores

In $I$ matched pairs, each with one treated and one control unit, let $Y_i$ be the treated-minus-control difference in pair $i$, and test the sharp null hypothesis of no treatment effect with a signed score statistic $T = \sum_i \operatorname{sgn}(Y_i)\, q_i$, where $\operatorname{sgn}(y) = \mathbf 1\{y > 0\}$ and $q_i \ge 0$ is a function of $|Y_i|$ with $q_i = 0$ when $Y_i = 0$. Rosenbaum's sensitivity model allows the odds of treatment within each pair to deviate from $1$ by at most a factor $\Gamma \ge 1$, with independent assignments in distinct pairs. Let $\overline T_\Gamma$ be the sum of independent variables taking the value $q_i$ with probability $\Gamma/(1 + \Gamma)$ and $0$ with probability $1/(1 + \Gamma)$, and $\underline T_\Gamma$ the same with $\Gamma$ replaced by $1/\Gamma$. Under the sharp null and the sensitivity model, conditionally on the potential outcomes and on the matched design,

$$P(\underline T_\Gamma \ge t) \le P(T \ge t) \le P(\overline T_\Gamma \ge t) \qquad \text{for all } t,$$

the bounds are attained for particular assignment probabilities in the model, and for $\Gamma = 1$ both equal the randomization distribution (Rosenbaum 2002, Section 4.4, as stated by Zhao 2017). The sign-test case, $q_i = 1$ for every pair with a nonzero difference and $q_i = 0$ for tied pairs, is [the binomial bounds on the sign-test tail](../../not-yet-classified/part-17/rosenbaum-sensitivity/upper-tail-bounds.md); this page states the bounds for general scores and their attainment.

## Expansion

1. The model: matched pairs, treatment assignment probabilities with bounded odds within pairs, and the sharp null hypothesis.
2. Under the sharp null, the positive-sign indicators of the pairs with nonzero differences are independent Bernoulli variables with success probabilities in $[1/(1 + \Gamma), \Gamma/(1 + \Gamma)]$.
3. Stochastic ordering of sums of independent weighted Bernoulli variables by their success probabilities, giving the bounding distributions, and their attainment.
4. The bounds for Wilcoxon's signed-rank statistic, $q_i = \operatorname{rank}(|Y_i|)$.
5. The normal approximation of the bounding distributions, as a separate statement, under Zhao's condition that no score dominates, $\max_i q_i^2 / \sum_i q_i^2 \to 0$; a large number of pairs alone does not suffice.

## Sources

- Q. Zhao, On sensitivity value of pair-matched observational studies, 2017, Section 2, equations (2.1)–(2.3). <https://arxiv.org/abs/1702.03442>
- Original result: P. R. Rosenbaum, Sensitivity analysis for certain permutation inferences in matched observational studies, Biometrika 74 (1987), 13–26. <https://doi.org/10.1093/biomet/74.1.13> The bounding distributions for signed score statistics follow Zhao (2017), who cites Rosenbaum (2002, Section 4.4).
