# Countable unions of uniformly convergent classes and countable classes are nonuniformly learnable

Let $X$, $Y$ be measurable spaces and $\mathcal{D}$ a family of distributions on $X \times Y$. Say a class $H$ has uniform convergence rate $\epsilon(m, \delta)$ over $\mathcal{D}$ if for all $D \in \mathcal{D}$, $m > 0$, $\delta > 0$, an i.i.d. sample of size $m$ is $\epsilon(m,\delta)$-representative for $H$ with probability at least $1 - \delta$. Let $H_1, H_2, \dots$ be countably many classes with rates $\epsilon_i$ such that $\epsilon_i(m, \delta) \to 0$ as $m \to \infty$ for every $\delta > 0$. Then $\bigcup_i H_i$ is nonuniformly learnable over $\mathcal{D}$: for each accuracy $\varepsilon$ and confidence $\delta$, a structural risk minimization rule over pairs $(i, h)$ with $h \in H_i$ and penalties $\mathrm{pen}_i = \epsilon_i(m, w_i\delta)$ (for a weighting $w_i > 0$, $\sum_i w_i \le 1$) satisfies, with probability at least $1 - \delta$, $L_D(A(S)) \le L_D(h) + 2\,\mathrm{pen}_i$ for every $i$ and $h \in H_i$, and for each fixed $h$ this excess is below $\varepsilon$ from some sample size on. In particular every countable class with measurable misclassification sets is nonuniformly learnable over all distributions, even when its VC dimension is infinite and it is not PAC learnable.

## Proof sketch

The weighted union bound makes the sample $\epsilon_i(m, w_i\delta)$-representative for every $H_i$ simultaneously with probability at least $1 - \delta$. On that event the SRM output $A(S)$ in class $j$ has $L_D(A(S)) \le L_S(A(S)) + \mathrm{pen}_j \le L_S(h) + \mathrm{pen}_i \le L_D(h) + 2\,\mathrm{pen}_i$. A countable class is the union of its singletons, each with the Hoeffding rate $\sqrt{\ln(2/\delta)/(2m)}$.

## Depends on

- [Nonuniform learnability and structural risk minimization](../../pac-learning/nonuniform-learnability-and-structural-risk-minimization.md)
- [Uniform convergence property and eps-representative samples](../../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
