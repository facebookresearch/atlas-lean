# Rosenbaum's sensitivity bounds for matched-pair sign tests

In $I$ matched pairs, each with one treated and one control unit, let $Y_i$ be the treated-minus-control difference in pair $i$, and test the sharp null hypothesis of no treatment effect with a signed score statistic $T = \sum_i \operatorname{sgn}(Y_i)\, q_i$, where $\operatorname{sgn}(y) = \mathbf 1\{y > 0\}$ and $q_i \ge 0$ is a function of $|Y_i|$ with $q_i = 0$ when $Y_i = 0$. Rosenbaum's sensitivity model allows the odds of treatment within each pair to deviate from $1$ by at most a factor $\Gamma \ge 1$, with independent assignments in distinct pairs. Let $\overline T_\Gamma$ be the sum of independent variables taking the value $q_i$ with probability $\Gamma/(1 + \Gamma)$ and $0$ with probability $1/(1 + \Gamma)$, and $\underline T_\Gamma$ the same with $\Gamma$ replaced by $1/\Gamma$. Under the sharp null and the sensitivity model, conditionally on the potential outcomes and on the matched design,

$$P(\underline T_\Gamma \ge t) \le P(T \ge t) \le P(\overline T_\Gamma \ge t) \qquad \text{for all } t,$$

the bounds are attained for particular assignment probabilities in the model, and for $\Gamma = 1$ both equal the randomization distribution (Rosenbaum 2002, Section 4.4, as stated by Zhao 2017). For the sign test, $q_i = 1$ for every pair with $Y_i \ne 0$: with $n$ such pairs the bounding variables are binomial, $\mathrm{Bin}(n, 1/(1 + \Gamma))$ and $\mathrm{Bin}(n, \Gamma/(1 + \Gamma))$, so the one-sided $p$-value lies between the two binomial tail probabilities for every $\Gamma$.

## Expansion

1. The model: matched pairs, treatment assignment probabilities with bounded odds within pairs, and the sharp null hypothesis.
2. Under the sharp null, the signs are independent Bernoulli variables with success probabilities in $[1/(1 + \Gamma), \Gamma/(1 + \Gamma)]$.
3. Stochastic ordering of sums of independent weighted Bernoulli variables by their success probabilities, giving the bounding distributions, and their attainment.
4. The binomial bounds for the sign test (McNemar's test for binary outcomes) and the bounds for Wilcoxon's signed-rank statistic, $q_i = \operatorname{rank}(|Y_i|)$.
5. The normal approximation of the bounding distributions for large $I$, as a separate statement.

## Sources

- Q. Zhao, On sensitivity value of pair-matched observational studies, 2017, Section 2, equations (2.1)–(2.3). <https://arxiv.org/abs/1702.03442>
- Original result: P. R. Rosenbaum, Sensitivity analysis for certain permutation inferences in matched observational studies, Biometrika 74 (1987), 13–26. <https://doi.org/10.1093/biomet/74.1.13> The bounding distributions for signed score statistics follow Zhao (2017), who cites Rosenbaum (2002, Section 4.4).
