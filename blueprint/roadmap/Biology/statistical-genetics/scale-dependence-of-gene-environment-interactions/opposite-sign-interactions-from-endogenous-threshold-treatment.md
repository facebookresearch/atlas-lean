# Opposite-sign interactions from endogenous threshold treatment

Let a phenotype $Y$ be additive in a genetic variant with effect $\beta_j$, and let an exposure $E$ (a treatment) be assigned endogenously, whenever $Y$ exceeds a threshold $t$, after which it changes $Y$ by a treatment effect $\alpha$ that lowers levels above the threshold. If the threshold exceeds the reference mean, $P_0 = t - \mu > 0$, the interaction estimated by regressing the observed phenotype on $G$, $E$ and $GE$ satisfies

$$\operatorname{sgn}(\hat\gamma_j) = -\operatorname{sgn}(\hat\beta_j).$$

So, like monotone convex rescaling, threshold-based treatment produces interactions whose signs are locked to the signs of the main genetic effects across variants; widespread sign consistency of observed $G \times E$ effects (for example, gene–age interactions on LDL cholesterol induced by statin use) therefore signals confounding by scale or by treatment rather than biological interaction.

## Depends on

- [Sign-consistent interactions under monotone convex transformations](sign-consistent-interactions-under-monotone-convex-transformations.md)

## Expansion

With a normally distributed phenotype, set $P_0 = t - E[Y \mid G_j = 0]$ and $P_1 = t - E[Y \mid G_j = 1]$, and let $\lambda(x) = \phi(x)/\Phi(x)$ be the inverse Mills ratio, which is decreasing and strictly convex. Truncated-normal moments give

$$E[\hat\beta_j] = \lambda(P_0) - \lambda(P_1) + P_0 - P_1,\qquad E[\hat\gamma_j] = \lambda(-P_1) - \lambda(-P_0) - \left(\lambda(P_0) - \lambda(P_1)\right).$$

Since $\lambda(P_0) - \lambda(P_1)$ has the sign opposite to $P_0 - P_1$ and smaller magnitude, $\hat\beta_j$ has the sign of $P_0 - P_1$; since $\lambda(-P_1) - \lambda(-P_0)$ has the same sign as $\lambda(P_0) - \lambda(P_1)$ and larger magnitude, $\hat\gamma_j$ has the sign of $\lambda(P_0) - \lambda(P_1)$, i.e. opposite to $\hat\beta_j$. The same holds when treatment is given below a threshold.

## Sources

- M. Sadowski, A. W. Dahl, N. Zaitlen and R. Border, "The geometry of G × E: how scaling and endogenous treatment effects shape interaction direction", *PLOS Genetics* (2026), Results, Theorem 3 and the derivation following it via the inverse Mills ratio, and the statin–LDL example. <https://doi.org/10.1371/journal.pgen.1012073> (PMC13043064)
