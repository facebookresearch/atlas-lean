# Natural direct and indirect effects: decomposition of the total effect

Let $X$ be a treatment, $Z$ a mediator and $Y$ an outcome, with counterfactuals $Y_x$, $Z_x$ and $Y_{xz}$ in a structural causal model, and let $x^*$ be the reference value of $X$. Pearl (2001) defines the average total, natural direct and natural indirect effects of the transition from $x^*$ to $x$ as

$$\mathrm{TE}(x, x^*; Y) = E(Y_x) - E(Y_{x^*}), \qquad \mathrm{NDE}(x, x^*; Y) = E(Y_{x, Z_{x^*}}) - E(Y_{x^*}), \qquad \mathrm{NIE}(x, x^*; Y) = E(Y_{x^*, Z_x}) - E(Y_{x^*}),$$

assuming these expectations are finite, and proves (Theorem 3)

$$\mathrm{TE}(x, x^*; Y) = \mathrm{NDE}(x, x^*; Y) - \mathrm{NIE}(x^*, x; Y), \qquad \mathrm{TE}(x, x^*; Y) = \mathrm{NIE}(x, x^*; Y) - \mathrm{NDE}(x^*, x; Y).$$

Both follow from $Y_{x, Z_x} = Y_x$ by adding and subtracting $E(Y_{x, Z_{x^*}})$, respectively $E(Y_{x^*, Z_x})$. In linear models, where the effect of a transition changes sign when the transition is reversed, they give $\mathrm{TE} = \mathrm{NIE} + \mathrm{NDE}$. Identification of the natural effects from observational data, by covariate adjustment or by the mediation formulas of [natural direct/indirect effects and the mediation formula](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-indirect-effects-and-the-mediation-formula.md), is a separate statement.

## Depends on

- [Natural direct/indirect effects and the mediation formula](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-indirect-effects-and-the-mediation-formula.md)

## Expansion

1. The model: a structural causal model with counterfactuals $Y_{xz}$, $Z_x$, the composition $Y_{x, Z_x} = Y_x$, and the definitions of total, controlled direct, natural direct and natural indirect effects.
2. The decomposition identities of Theorem 3, and the additive relation in linear models, where the indirect effect is the product of the treatment–mediator and mediator–outcome coefficients.
3. Separate target: identification by adjusting for a covariate set $W$ of nondescendants of $X$ and $Z$ (Pearl 2001, Theorems 1, 2 and 4), with the counterfactual conditional-independence condition (7) of the source, positivity of the conditional laws involved, and the resulting adjustment formulas for the natural direct and indirect effects, including the graphical criterion of Corollary 1.

## Sources

- J. Pearl, Direct and indirect effects, in *Proc. 17th Conference on Uncertainty in Artificial Intelligence*, 2001, 411–420, Definitions 4–7, Theorems 1–4, equations (17) and (21)–(27). <https://arxiv.org/abs/1301.2300>
