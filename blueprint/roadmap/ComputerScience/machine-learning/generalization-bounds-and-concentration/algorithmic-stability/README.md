# Algorithmic stability

An algorithm is uniformly stable if replacing one example of its training sample changes the loss of its output at every test example by at most $\varepsilon$. Uniform stability bounds the expected generalization gap by $\varepsilon$, with no reference to the size or complexity of the class of predictors the algorithm may output (Bousquet and Elisseeff 2002; Hardt, Recht and Singer 2016, Theorem 2.2). The proof is an exchange argument: replacing a training example by a fresh one does not change the law of the sample. The generalization bound below is stated for a bounded, jointly measurable loss.

- [Uniform stability](is-uniformly-stable.md)
- [Replace-one sampling preserves the law of an i.i.d. sample](map-update-prod-pi.md)
- [Uniform stability implies generalization in expectation](abs-integral-empirical-risk-sub-risk-le.md)
- [On-average replace-one stability](on-average-replace-one-stability.md)
- [Expected generalization gap equals replace-one stability term](expected-generalization-gap-equals-replace-one-stability-ter.md)
- [Uniform stability implies high-probability generalization](uniform-stability-implies-high-probability-generalization.md)
- [Deletion stability bounds replacement stability](deletion-stability-bounds-replacement-stability.md)

## Stability of stochastic gradient descent

Stochastic gradient descent on convex, $\beta$-smooth, $L$-Lipschitz losses with steps $\alpha_t \le 2/\beta$ is uniformly stable with $\varepsilon \le (2L^2/n)\sum_t \alpha_t$ (Hardt, Recht and Singer, Theorem 3.8). The proof couples the runs on two samples that differ in one example through the same random indices: a step on a shared example applies the same non-expansive gradient update to both runs, and a step on the differing example, which happens with probability $1/n$, moves them apart by at most $2\alpha_t L$. With the generalization bound above, applied to a loss bounded at the starting point (each step moves the iterate by at most $\alpha_t L$, so the losses along the run stay bounded), the expected generalization gap of SGD is at most $2L^2/n$ times its total step length, whatever the number of passes over the data: training faster generalizes better.

- [Iterates of the stochastic gradient method](sgm-iterate.md)
- [Output of the stochastic gradient method](sgm-output.md)
- [Random selection rule](index-measure.md)
- [Growth recursion for two bounded updates](norm-sub-le-min-mul-add-two-mul.md)
- [Coupled distance of SGM along a fixed index sequence](norm-sgm-iterate-sub-le.md)
- [Uniform stability of SGM for convex, smooth, Lipschitz losses](integral-abs-sgm-output-sub-le.md)
- [SGM is uniformly stable](is-uniformly-stable-sgm.md)
- [SGM moves at most $L \sum_t \alpha_t$ from its start](norm-sgm-iterate-sub-start-le.md)
- [Generalization of SGM in expectation](abs-integral-empirical-risk-sub-risk-sgm.md)
- [Dataset swap identity](swap-identity.md)

## High-probability generalization from deletion stability

- [Is Deletion Stable](is-deletion-stable.md)
- [Leave One Out Risk](leave-one-out-risk.md)

## Related topics

- [Rademacher complexity](../rademacher-complexity/README.md): the uniform-convergence route to generalization, which bounds the deviation of every predictor of a class at once, where stability bounds only that of the predictor the algorithm returns.
- [Gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/README.md): the expansiveness of the gradient step (co-coercivity, non-expansiveness for steps up to $2/\beta$, the $\alpha L$ bound) used by the stability of SGD, and the convergence rates of SGD, which improve with the total step length while the stability bound degrades.
