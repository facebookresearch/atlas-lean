# Omnipredictors for constrained loss minimization

Omniprediction extends to constrained loss minimization: there are predictors which can be post-processed to minimize any loss from a rich family subject to constraints from a family (for example, group-wise fairness constraints such as statistical parity or equal opportunity across subpopulations), competing with the best hypothesis of $\mathcal{C}$ that satisfies the constraints, as long as the subpopulations used to define the constraints are identifiable by the class. With groups given by $g : X \to [t]$, objectives and constraints $f(x, a, y)$ that depend on $x$ only through $g(x)$, and differences $\partial f(x,a) = f(x,a,1) - f(x,a,0)$, such omnipredictors are implied by group-wise conditions: for actions in $[0,1]$, group multiaccuracy with respect to $\mathcal{C}$ plus group calibration, with error parameters $\varepsilon/6$, when all objectives and constraints are convex and special ($\partial f(x,a) = \tau_1(g(x)) + \tau_2(g(x))\,a$ with coefficients $\tau_1, \tau_2 : [t] \to [-1,1]$, which covers linear fairness constraints such as statistical parity, equal opportunity and equalized odds); for actions in $[0,1]$, group multicalibration plus group calibration, with error parameters $\varepsilon/15$, for convex $1$-Lipschitz objectives and constraints with $1$-bounded differences ($|\partial f| \le 1$); and, for a finite nonempty action set $A$ and general group constraints and objectives with $1$-bounded differences, group level-set multiaccuracy plus group calibration, with error parameters $\varepsilon/3$, where the post-processings are randomized, $c(x) = \tau(g(x), p(x)) \in \Delta(A)$. The task is then solved on the simulated distribution $D_p$, in which $y \sim \mathrm{Ber}(p(x))$, over post-processings $c(x) = \tau(g(x), p(x))$ that depend on the group and the prediction, with the tolerances of the definition: if $\beta^*$ is the optimal objective over constraint-satisfying $c \in \mathcal{C}$ on $D$ and $\beta$ the optimal objective over post-processings whose constraints are violated by at most $\varepsilon/3$ on $D_p$ (both assumed finite), then every post-processing with objective at most $\beta + \varepsilon/3$ and constraint violation at most $2\varepsilon/3$ on $D_p$ has objective at most $\beta^* + \varepsilon$ and constraint violation at most $\varepsilon$ on $D$.

## Proof sketch

The group-wise conditions make the expected value of every objective and constraint function nearly the same under $D$ and under $D_p$, both for each $c \in \mathcal{C}$ (via group multiaccuracy or multicalibration, using convexity to replace $c$ by its group- and level-set-wise averages) and for each post-processing $\tau(g(x), p(x))$ (via group calibration). Hence the constrained optimum over $\mathcal{C}$ on $D$ is matched by a group-and-prediction post-processing on $D_p$, and a solution found on $D_p$ transfers back to $D$. The groups are fixed before learning, while the objectives and constraints may be chosen afterwards.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)
- [Group fairness criteria for scores and classifiers](../algorithmic-fairness/group-fairness-criteria-for-scores-and-classifiers.md)

## Proof depends on

- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)

## Sources

- L. Hu, I. Livni-Navon, O. Reingold, C. Yang, "Omnipredictors for Constrained Optimization", ICML (2023), arXiv:2209.07463, Definitions 2.1, 4.2, 4.3 and 4.5, Theorems 4.4, 4.6 and 4.7.
