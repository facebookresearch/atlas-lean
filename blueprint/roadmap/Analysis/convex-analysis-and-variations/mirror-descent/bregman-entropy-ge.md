# Strong convexity of the entropy on the simplex with respect to $\|\cdot\|_1$

For $x$ in the [relative interior of the simplex](pos-simplex.md) and $u$ in the [simplex](simplex.md), vertices included,

$$
V_x(u) \ge \tfrac12 \|u - x\|_1^2 ,
$$

that is, the [entropy](entropy.md) is $1$-strongly convex with respect to $\|\cdot\|_1$ in the Bregman form used by mirror descent, with iterates in the relative interior and comparators anywhere in the simplex. By the [Kullback–Leibler formula](bregman-entropy-eq.md) this is Pinsker's inequality $\|u - x\|_1^2 \le 2\,\mathrm{KL}(u \,\|\, x)$ for a probability vector $u$ with zero entries allowed; the source proves the modulus instead from the Hessian, $h^T \nabla^2\omega(x) h = \sum_i h_i^2/x_i \ge \|h\|_1^2$ by the Cauchy–Schwarz inequality.

## Background

- [Csiszár–Kullback–Pinsker inequality with zero entries allowed](../../../InformationTheory/information-inequalities/csiszar-kullback-pinsker-of-nonneg.md): applied to $u$ and $x$, it replaces the source's Hessian computation.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example ($\alpha = 1$), and the appendix (entropy as a distance-generating function on the standard simplex).
