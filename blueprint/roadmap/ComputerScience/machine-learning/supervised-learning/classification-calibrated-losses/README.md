# Classification-calibrated losses

Surrogate losses $\varphi$ that replace the 0-1 loss in convex risk minimization (the hinge loss of support vector machines, the exponential loss of AdaBoost, the logistic loss), and the condition of Bartlett, Jordan and McAuliffe under which minimizing the $\varphi$-risk forces the sign of the Bayes classifier: classification calibration. For convex $\varphi$ it reduces to differentiability at $0$ with $\varphi'(0) < 0$. Bartlett, Jordan and McAuliffe also give the quantitative comparison $\psi(R(f) - R^*) \le R_\varphi(f) - R_\varphi^*$ through the $\psi$-transform (their Theorem 3).

- [Conditional surrogate risk](cond-risk.md)
- [Optimal conditional surrogate risk](opt-risk.md)
- [Optimal conditional surrogate risk with the wrong sign](wrong-sign-risk.md)
- [Classification-calibrated loss](is-classification-calibrated.md)
- [Convex losses with negative slope at 0 are classification-calibrated](is-classification-calibrated-of-has-deri.md)

## Supporting lemmas

- [The case eta greater than one half](opt-risk-lt-wrong-sign-risk-of-half-lt.md)
- [Reflection of the conditional risk](cond-risk-one-sub.md)
- [Symmetry of the optimal risks](opt-risk-one-sub.md)
- [Symmetry of the wrong-sign risks](wrong-sign-risk-one-sub.md)

## Related topics

- [Bayes classifier](../bayes-classifier/README.md): the target whose sign a calibrated surrogate recovers.
- [Cross-entropy loss](../cross-entropy-loss/README.md): the logistic loss is the binary cross-entropy written as a margin loss.
- [AdaBoost](../../online-learning-and-boosting/adaboost/README.md): minimizes the exponential loss, a calibrated surrogate.
