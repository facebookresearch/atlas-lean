# Learners and agnostic PAC learnability

This node covers learners and agnostic PAC learnability for a general loss, with expected and empirical risk as on
the pages linked below.

## Expansion

A sound expansion has separate pages for:

1. **Learners.** A learner is a measurable map from samples of each size $m \ge 1$ to hypotheses; proper learners
   output members of $H$.
2. **Agnostic PAC learnability.** For a loss $\ell : H \times Z \to [0, \infty)$ with finite expected risk $L_D$, There are $m_H : (0,1)^2 \to \mathbb{N}$ and a learner $A$ such that for all
   $\varepsilon, \delta \in (0,1)$, every $D$ and every $m \ge m_H(\varepsilon, \delta)$,
   $\Pr_{S \sim D^m}[L_D(A(S)) > \inf_{h \in H} L_D(h) + \varepsilon] \le \delta$; the sample complexity is the pointwise
   least such $m_H$. The realizable notion is the existing one and is linked, not redefined.

## Depends on

- [Expected risk](../../generalization-bounds-and-concentration/risk.md)
- [Empirical risk](../../generalization-bounds-and-concentration/empirical-risk.md)

## Related topics

- [The 0-1 loss as an abstract loss](../risk-of-the-0-1-loss/zero-one-loss.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definitions 3.1 and 3.4 (PAC and agnostic PAC learnability for general loss functions). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
