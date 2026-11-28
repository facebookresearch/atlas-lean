# Bayes rule for binary classification with misclassification costs

Let $P_0$ and $P_1$ be probability measures on a measurable space $(\mathcal X, \mathcal A)$, the class-conditional laws, with measurable densities $p_0, p_1 \ge 0$ with respect to a measure $\mu$. Let $\pi_0, \pi_1 > 0$ with $\pi_0 + \pi_1 = 1$ be the prior probabilities of the two classes, and let $C_{yk}$ be the cost of deciding $y$ when the class is $k$, with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. A randomized decision rule is a Markov kernel $\kappa$ from $\mathcal X$ to $\{0, 1\}$, and its Bayes average cost is

$$R(\kappa) = \pi_0 \int \!\! \int C_{y0}\, \kappa(x, dy)\, P_0(dx) + \pi_1 \int \!\! \int C_{y1}\, \kappa(x, dy)\, P_1(dx).$$

The deterministic rule $\delta^*(x) = 1$ if $\pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x)$ and $\delta^*(x) = 0$ if the reverse strict inequality holds, with either fixed value on the tie set, is measurable and satisfies $R(\delta^*) \le R(\kappa)$ for every randomized rule $\kappa$. Under 0–1 loss, $C_{00} = C_{11} = 0$ and $C_{01} = C_{10} = 1$, it decides $1$ exactly when $\pi_1 p_1(x) > \pi_0 p_0(x)$, up to ties.

## Background

- [Neyman–Pearson lemma for two dominated simple hypotheses](../../../hypothesis-testing/neyman-pearson-dominated-two-simple.md)
- [A posterior argmax classifier has minimal 0-1 risk](../../../../ComputerScience/machine-learning/supervised-learning/bayes-classifier/avg-risk-le.md), the same optimality for a joint law of input and label

## Sources

- T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press, 1967 (Bayes tests of a simple hypothesis against a simple alternative)
