# Natural direct and indirect effects: decomposition and identification by adjustment

Let $X$ be a treatment, $Z$ a mediator and $Y$ an outcome, with counterfactuals $Y_x$, $Z_x$ and $Y_{xz}$, and let $x^*$ be the reference value of $X$. Pearl (2001) defines the average natural direct and indirect effects of the transition from $x^*$ to $x$ as

$$\mathrm{NDE}(x, x^*; Y) = E(Y_{x, Z_{x^*}}) - E(Y_{x^*}), \qquad \mathrm{NIE}(x, x^*; Y) = E(Y_{x^*, Z_x}) - E(Y_{x^*}),$$

and proves:

1. (Theorem 3) With the total effect $\mathrm{TE}(x, x^*; Y) = E(Y_x) - E(Y_{x^*})$, one has $\mathrm{TE}(x, x^*; Y) = \mathrm{NDE}(x, x^*; Y) - \mathrm{NIE}(x^*, x; Y)$ and $\mathrm{TE}(x, x^*; Y) = \mathrm{NIE}(x, x^*; Y) - \mathrm{NDE}(x^*, x; Y)$; in linear models, where the effect of a transition changes sign when the transition is reversed, these give $\mathrm{TE} = \mathrm{NIE} + \mathrm{NDE}$.
2. (Theorems 1, 2 and 4) If there is a set $W$ of covariates, nondescendants of $X$ and $Z$, satisfying the counterfactual independence condition (7) of the source, the natural direct and indirect effects are identified by adjusting for $W$.

In the unconfounded finite case these identifications reduce to the mediation formulas, which are stated on [natural direct/indirect effects and the mediation formula](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-indirect-effects-and-the-mediation-formula.md).

## Depends on

- [Natural direct/indirect effects and the mediation formula](../../../ComputerScience/machine-learning/probabilistic-graphical-models/natural-direct-indirect-effects-and-the-mediation-formula.md)

## Expansion

1. The model: a structural causal model with counterfactuals $Y_{xz}$, $Z_x$, and the definitions of total, controlled direct, natural direct and natural indirect effects.
2. The decomposition identities of Theorem 3 and the additive relation in linear models, where the indirect effect is the product of the treatment–mediator and mediator–outcome coefficients.
3. The identification conditions with a covariate set $W$, including the graphical criterion of Corollary 1.

## Sources

- J. Pearl, Direct and indirect effects, in *Proc. 17th Conference on Uncertainty in Artificial Intelligence*, 2001, 411–420, Definitions 4–7, Theorems 1–4, equations (17) and (21)–(27). <https://arxiv.org/abs/1301.2300>
