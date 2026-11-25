# The back-door adjustment

**The back-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.2): let $B$ be a Bayesian
network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type $\alpha$ and joint
distribution $P$, and let $P_{\mathrm{do}(X_k = a)}$ be the joint distribution of the
[intervention](intervene.md) $\mathrm{do}(X_k = a)$. Let $k \ne y$ be a treatment node and an
outcome node, and let $Z$ be a finite set of nodes with $y \notin Z$ that contains no descendant of
$k$ and blocks every path between $k$ and $y$ that begins with an arrow into $k$. Assume that
$P(X_k = a, X_Z = z) \ne 0$ whenever $P(X_Z = z) \ne 0$. Then for every $v \in \alpha$,

$$P_{\mathrm{do}(X_k = a)}(X_y = v) = \sum_{z \in \alpha^Z} P(X_Z = z) \, \frac{P(X_k = a, X_y = v, X_Z = z)}{P(X_k = a, X_Z = z)},$$

where $P(E)$ is the sum of $P(x)$ over the configurations $x \in \alpha^n$ in $E$, and a term
with $P(X_Z = z) = 0$ is $0$.

## Background

- [Strong ignorability](../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/strongly-ignorable.md):
  the potential-outcome condition under which the same adjustment formula holds; Pearl (2009,
  *Statistics Surveys*, §4.2, eqs. (39)–(40)) explains the back-door criterion as a graphical
  test for conditional ignorability.
- [Rule 2 of the do-calculus](do-calculus-rule2.md) and
  [Rule 3 of the do-calculus](do-calculus-rule3.md): the symbolic calculus that Pearl (1995, §4)
  introduces to derive causal-effect formulas such as this one step by step.
