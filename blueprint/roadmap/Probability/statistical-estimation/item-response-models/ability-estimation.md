# Existence of the maximum-likelihood ability estimate in the two-parameter logistic model

In the [two-parameter logistic model](two-parameter-logistic-model.md), let $J$ be a finite nonempty set of items with discriminations $a_j > 0$ and difficulties $b_j$, let $P_j(\theta) = \bigl(1 + e^{-a_j(\theta - b_j)}\bigr)^{-1}$, and let $x \in \{0, 1\}^J$ be a response pattern. The log-likelihood of the ability,

$$\ell(\theta) = \sum_{j \in J} \bigl(x_j \log P_j(\theta) + (1 - x_j) \log(1 - P_j(\theta))\bigr),$$

is strictly concave on $\mathbb R$, with $\ell''(\theta) = -\sum_j a_j^2 P_j(\theta)(1 - P_j(\theta)) < 0$. It attains its maximum if and only if the pattern is neither all correct nor all incorrect, and then the maximizer $\hat\theta$ is unique and is the unique root of the score $\ell'(\theta) = \sum_j a_j\bigl(x_j - P_j(\theta)\bigr)$. For the all-correct pattern $\ell$ increases to $0$ as $\theta \to \infty$, and for the all-incorrect pattern as $\theta \to -\infty$, so no estimate exists. The Rasch model is the case $a_j = 1$. Confidence intervals, asymptotic normality as the number of items grows, and the finite-test bias of $\hat\theta$ need further hypotheses and are separate results.

## Depends on

- [Two-parameter logistic model](two-parameter-logistic-model.md)

## Sources

- F. M. Lord, *Applications of Item Response Theory to Practical Testing Problems*, Lawrence Erlbaum, 1980
