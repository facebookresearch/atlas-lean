# Sign-consistent interactions under monotone convex transformations

For a genetic variant $G$ and an environmental exposure $E$, fit the regression

$$\varphi(Y) = \hat\mu^\varphi + \hat\alpha^\varphi E + \hat\beta^\varphi G + \hat\gamma^\varphi GE + \varepsilon^\varphi$$

of a transformed phenotype $\varphi(Y)$. Suppose that on the original scale $Y$ has homogeneous variance, $G$ and $E$ act additively (the fitted interaction $\hat\gamma$ of $Y$ on $G$, $E$, $GE$ is zero), and $G$ and $E$ are independent, mean-centred, with finite variance.

1. **Sign rule.** If $\varphi$ is a monotone convex (or concave) transformation, then

$$\operatorname{sgn}(\hat\gamma^\varphi) = \operatorname{sgn}(\varphi'')\cdot\operatorname{sgn}(\hat\alpha^\varphi)\cdot\operatorname{sgn}(\hat\beta^\varphi).$$

Consequently, for several variants coded so that their main effects share a sign, all induced interactions have the same sign (sign consistency). By contraposition, interactions of both signs relative to the main effects cannot all be produced by one monotone convex rescaling.

2. **Diploid genotypes.** The rule extends to $G \in \{0,1,2\}$ under Hardy–Weinberg equilibrium and to any exposure $E$ satisfying the same independence and moment conditions.
3. **Correlated $G$ and $E$.** With gene–environment correlation, $\hat\gamma^\varphi \approx \gamma_{\text{corr}} + \alpha\beta\,E[\varphi''(\varepsilon)]$, where $\gamma_{\text{corr}}$ comes from non-orthogonal predictors; the sign rule holds whenever $|\alpha\beta\,E[\varphi'']| > |\gamma_{\text{corr}}|$, in particular for weak correlation or strong curvature.

Exponential, logarithmic, square-root and power transformations are all monotone and convex or concave on their domains.

## Depends on

- [Hardy–Weinberg equilibrium](../../../population-genetics/hardy-weinberg-law/offspring-offspring.md)

## Expansion

By a second-order Taylor expansion of $\varphi$ around the additive mean $\mu + \alpha E + \beta G$, the cross term of $\tfrac12\varphi''\,(\alpha E + \beta G)^2$ is $\varphi''\alpha\beta\,GE$, so curvature converts two additive main effects into an interaction with the sign of $\varphi''\alpha\beta$; homoscedasticity and independence ensure no other source contributes an interaction, and monotonicity preserves the signs of the main effects after transformation.

## Sources

- M. Sadowski, A. W. Dahl, N. Zaitlen and R. Border, "The geometry of G × E: how scaling and endogenous treatment effects shape interaction direction", *PLOS Genetics* (2026), Results, Theorem 1, Corollary 1, Theorem 2 and Corollary 2, with proofs in S1 Appendix. <https://doi.org/10.1371/journal.pgen.1012073> (PMC13043064)
