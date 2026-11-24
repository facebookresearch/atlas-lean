# Bayes rule for binary classification under 0–1 loss

Let $P_0$ and $P_1$ be finite measures on a measurable space $(\mathcal X, \mathcal A)$, the class-conditional laws, and $\pi_0, \pi_1 \ge 0$ prior weights. Write $p_0, p_1$ for densities of $P_0, P_1$ with respect to $\nu = P_0 + P_1$. For a measurable decision rule $\delta : \mathcal X \to \{0, 1\}$, the Bayes risk under 0–1 loss is

$$R(\delta) = \pi_0\, P_0(\delta = 1) + \pi_1\, P_1(\delta = 0).$$

The rule $\delta^*(x) = 1$ if $\pi_1 p_1(x) > \pi_0 p_0(x)$ and $\delta^*(x) = 0$ otherwise minimizes $R$ over all decision rules, with minimal risk $R(\delta^*) = \int \min(\pi_0 p_0, \pi_1 p_1)\, d\nu$; any assignment on the tie set $\{\pi_1 p_1 = \pi_0 p_0\}$ gives the same risk. Unequal misclassification costs $c_0, c_1 > 0$ reduce to this case by replacing $\pi_k$ with $c_k \pi_k$.

## Background

- [Neyman–Pearson lemma for two dominated simple hypotheses](neyman-pearson-dominated-two-simple.md)
- [A posterior argmax classifier has minimal 0-1 risk](../../ComputerScience/machine-learning/supervised-learning/bayes-classifier/avg-risk-le.md), the same optimality for a joint law of input and label

## Sources

- T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press, 1967, Section 6.1 (Bayes tests of a simple hypothesis against a simple alternative)
