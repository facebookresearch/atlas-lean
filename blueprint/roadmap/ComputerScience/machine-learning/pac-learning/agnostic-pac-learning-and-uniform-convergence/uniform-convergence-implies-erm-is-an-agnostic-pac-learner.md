# Uniform convergence implies ERM is an agnostic PAC learner

Let $H$ be a hypothesis class with a loss and $D$ a distribution. On an $(\varepsilon/2)$-representative sample, every
empirical risk minimizer $h_S \in H$ has $L_D(h_S) \le \inf_{h \in H} L_D(h) + \varepsilon$ (the deterministic comparison of
the page linked under Proof depends on), and an approximate minimizer with empirical excess at most $\eta$
satisfies the bound with $\varepsilon + \eta$. Consequently, if $H$ has the uniform convergence property with
sample complexity $m^{UC}_H$, then ERM is an agnostic PAC learner for $H$ with
$m_H(\varepsilon, \delta) \le m^{UC}_H(\varepsilon/2, \delta)$, under the measurability conditions that make the events
defined.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Empirical risk minimization (ERM) rule.

## Depends on

- [Uniform convergence property and eps-representative samples](uniform-convergence-property-and-eps-representative-samples.md)
- [Learners and agnostic PAC learnability](learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Empirical risk minimization under a uniform deviation bound](../../generalization-bounds-and-concentration/risk-le-add-two-mul-of-forall-abs-sub-le.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Lemma 4.2 and Corollary 4.4. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
