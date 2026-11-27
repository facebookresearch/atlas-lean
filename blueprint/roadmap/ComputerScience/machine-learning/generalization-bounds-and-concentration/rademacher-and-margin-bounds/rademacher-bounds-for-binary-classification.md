# Rademacher and VC bounds for binary classification

Let $C$ be a class of functions $\alpha \to \{0,1\}$ on a finite domain, $D$ a distribution on $\alpha \times \{0,1\}$ and $\sigma(C) = \{x \mapsto 2c(x) - 1 : c \in C\}$ its sign class. On every labelled sample, the empirical Rademacher complexity of the 0-1 loss class $\{(x,y) \mapsto [c(x) \ne y]\}$ is half that of $\sigma(C)$ on the unlabelled points, and the same holds for the Rademacher complexities under $D$ and its marginal. Consequently, for $m > 0$ and $\delta \in (0,1)$, with probability at least $1 - \delta$ every $h \in C$ satisfies

$$
\mathrm{err}_D(h) \le \mathrm{err}_S(h) + R_m(\sigma(C)) + \sqrt{\frac{\ln(1/\delta)}{2m}},
$$

and the data-dependent bound with $\hat{R}_{S_X}(\sigma(C))$ and $3\sqrt{\ln(2/\delta)/(2m)}$. Bounding the Rademacher complexity through the growth function gives $\mathrm{err}_D(h) \le \mathrm{err}_S(h) + \sqrt{2\ln\Pi_C(m)/m} + \sqrt{\ln(1/\delta)/(2m)}$, and, if every shattered set has at most $d$ points with $1 \le d \le m$, $\sqrt{2d\ln(em/d)/m}$ in place of the middle term. For an empirical risk minimizer $A$, with probability at least $1 - \delta$, $\mathrm{err}_D(A(S)) \le \mathrm{err}_D(c) + R_m(\sigma(C)) + \sqrt{2\ln(2/\delta)/m}$ for every $c \in C$.

## Proof sketch

The loss of $h$ at $(x, y)$ is $(1 - y'\,\sigma_h(x))/2$ with $y' = \pm 1$, and multiplying Rademacher signs by fixed signs does not change their law, which gives the halving identity. The generalization bound applies to the loss class with $[a,b] = [0,1]$; Massart's lemma over at most $\Pi_C(m)$ sign patterns and Sauer's lemma give the corollaries; the ERM bound combines the uniform bound with Hoeffding's inequality for the comparator.

## Depends on

- [Rademacher generalization bound for bounded function classes](rademacher-generalization-bound.md)
- [Rademacher complexity of a VC class, explicit rate](../rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md)
- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Growth function](../../pac-learning/sample-complexity-and-combinatorial-dimensions/growth-function-and-sauer-closed-form/growth-function.md)

## Proof depends on

- [Rademacher generalization bound for bounded function classes](rademacher-generalization-bound.md)
- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Sauer bound for the growth function](../../pac-learning/sample-complexity-and-combinatorial-dimensions/growth-function-and-sauer-closed-form/growth-function-le-sum.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
