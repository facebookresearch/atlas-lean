# Natural direct and indirect effects: decomposition of the total effect

Let $X$ be a treatment, $Z$ a mediator and $Y$ an outcome, with counterfactuals $Y_x$, $Z_x$ and $Y_{xz}$ in a structural causal model, and let $x^*$ be the reference value of $X$. Pearl (2001) defines the average total, natural direct and natural indirect effects of the transition from $x^*$ to $x$ as

$$\mathrm{TE}(x, x^*; Y) = E(Y_x) - E(Y_{x^*}), \qquad \mathrm{NDE}(x, x^*; Y) = E(Y_{x, Z_{x^*}}) - E(Y_{x^*}), \qquad \mathrm{NIE}(x, x^*; Y) = E(Y_{x^*, Z_x}) - E(Y_{x^*}),$$

assuming these expectations are finite, and proves (Theorem 3)

$$\mathrm{TE}(x, x^*; Y) = \mathrm{NDE}(x, x^*; Y) - \mathrm{NIE}(x^*, x; Y), \qquad \mathrm{TE}(x, x^*; Y) = \mathrm{NIE}(x, x^*; Y) - \mathrm{NDE}(x^*, x; Y).$$

Both follow directly from the definitions (6), (20) and (21) by adding and subtracting $E(Y_{x, Z_{x^*}})$, respectively $E(Y_{x^*, Z_x})$. The composition property $Y_{x, Z_x} = Y_x$ is used in the characterization that follows. Consequently

$$\mathrm{TE}(x, x^*; Y) = \mathrm{NDE}(x, x^*; Y) + \mathrm{NIE}(x, x^*; Y)$$

holds if and only if $\mathrm{NDE}(x, x^*; Y) = -\mathrm{NDE}(x^*, x; Y)$, that is, if and only if the expected direct contrast is the same at the two natural mediator values,

$$E\bigl(Y_{x, Z_x} - Y_{x^*, Z_x}\bigr) = E\bigl(Y_{x, Z_{x^*}} - Y_{x^*, Z_{x^*}}\bigr),$$

since, expanding the definitions with $Y_{x, Z_x} = Y_x$, the left side minus the right side equals $\mathrm{TE}(x, x^*; Y) - \mathrm{NDE}(x, x^*; Y) - \mathrm{NIE}(x, x^*; Y)$. A sufficient condition is an outcome equation additive in treatment and mediator, $Y_{x, z} = g_1(x) + g_2(z) + \varepsilon$ with $\varepsilon$ not depending on $(x, z)$, with no treatment–mediator interaction; linearity in the regression coefficients alone is not sufficient, since a model linear in its coefficients may contain an interaction term $\beta_{xz}\, xz$, under which the two contrasts differ by $\beta_{xz}(x - x^*)\,E(Z_x - Z_{x^*})$. Identification of the natural effects from observational data, by covariate adjustment or by the mediation formulas for [the natural direct effect](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-and-indirect-effects/nde-eq-mediation-formula-nde.md) and [the natural indirect effect](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-and-indirect-effects/nie-eq-mediation-formula-nie.md), is a separate statement.

## Expansion

1. The model: a structural causal model with counterfactuals $Y_{xz}$, $Z_x$, the composition $Y_{x, Z_x} = Y_x$, and the definitions of total, controlled direct, natural direct and natural indirect effects.
2. The decomposition identities of Theorem 3, the characterization of $\mathrm{TE} = \mathrm{NDE} + \mathrm{NIE}$ by equal expected direct contrasts, and the additive model without interaction, where in the linear case the indirect effect is the product of the treatment–mediator and mediator–outcome coefficients.
3. Separate targets: experimental identification of the natural effects from the interventional distributions (Pearl 2001, Theorems 1 and 4), with the counterfactual conditional-independence condition (7) and positivity; and observational identification by adjusting for a covariate set $W$ of nondescendants of $X$ and $Z$ (Theorem 2(ii)–(iii)), which in addition requires the two component interventional distributions to be identified, with the resulting adjustment formulas and the graphical criterion of Corollary 1.

## Related topics

- [Natural direct and indirect effects](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-and-indirect-effects/README.md)

## Sources

- J. Pearl, Direct and indirect effects, in *Proc. 17th Conference on Uncertainty in Artificial Intelligence*, 2001, 411–420, Definitions 4–7, Theorems 1–4, equations (17) and (21)–(27). <https://arxiv.org/abs/1301.2300>
