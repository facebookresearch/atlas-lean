# Instrumental inequality and Balke-Pearl bounds

Consider a structural causal model with binary instrument $Z$, treatment $X$ and outcome $Y$ and a latent
variable $U$, in which $Z$ is independent of $U$, $X$ is a function of $(Z, U)$, and $Y$ is a function of
$(X, U)$ only (no direct effect of $Z$ on $Y$). Assume $P(Z = z) > 0$ for both values of $z$. Then:

1. **Instrumental inequality.** $\max_x \sum_y \max_z P(X = x, Y = y \mid Z = z) \le 1$ (Pearl 1995, Theorem 1, Eq. (3); for
   binary variables it is the four inequalities of Eq. (8)).
2. **Balke–Pearl bounds.** Writing the model through the distribution of the response types of $X$
   (four functions of $z$) and of $Y$ (four functions of $x$), the set of values of the average causal
   effect $P(Y = 1 \mid \mathrm{do}(X = 1)) - P(Y = 1 \mid \mathrm{do}(X = 0))$ compatible with the
   observed $P(x, y \mid z)$ is the interval between the optima of two linear programs over the
   sixteen response-type classes; the bounds are sharp, and Balke and Pearl give them in closed form as maxima and
   minima of linear expressions in the eight observed probabilities $P(y, x \mid z)$ (JASA 1997, Section 3).

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite recursive structural causal models.

## Sources

- J. Pearl, *On the testability of causal models with latent and instrumental variables*, UAI 1995, Theorem 1 (Eq. (3)) and Eq. (8). <https://arxiv.org/pdf/1302.4976>
- A. Balke and J. Pearl, *Bounds on treatment effects from studies with imperfect compliance*, Journal of the American Statistical Association 92 (1997) 1171–1176, Sections 2–3 (the model with $Z$ independent of $U$ and no direct effect of $Z$ on $Y$, the linear program over sixteen response classes, and the closed-form bounds on the average causal effect, stated there to be the tightest possible).
- A. Balke and J. Pearl, *Counterfactual probabilities: computational methods, bounds and applications*, UAI 1994, Section 4.1 (the linear program over response-function distributions). <https://arxiv.org/pdf/1302.6784>
