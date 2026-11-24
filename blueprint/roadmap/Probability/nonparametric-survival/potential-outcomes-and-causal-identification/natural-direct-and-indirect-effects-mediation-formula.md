# Natural direct and indirect effects: the mediation formula

Let $X$ be a treatment, $Z$ a mediator and $Y$ an outcome, with counterfactuals $Y_x$, $Z_x$ and $Y_{xz}$, and let $x^*$ be the reference value of $X$. Pearl (2001) defines the average natural direct effect and the average natural indirect effect of the transition from $x^*$ to $x$ as
$$\mathrm{NDE}(x, x^*; Y) = E(Y_{x, Z_{x^*}}) - E(Y_{x^*}), \qquad \mathrm{NIE}(x, x^*; Y) = E(Y_{x^*, Z_x}) - E(Y_{x^*}),$$
and proves:

1. (Theorem 3) With the total effect $\mathrm{TE}(x, x^*; Y) = E(Y_x) - E(Y_{x^*})$, one has $\mathrm{TE}(x, x^*; Y) = \mathrm{NDE}(x, x^*; Y) - \mathrm{NIE}(x^*, x; Y)$ and $\mathrm{TE}(x, x^*; Y) = \mathrm{NIE}(x, x^*; Y) - \mathrm{NDE}(x^*, x; Y)$; in linear models, where the effect of a transition changes sign when the transition is reversed, these give $\mathrm{TE} = \mathrm{NIE} + \mathrm{NDE}$.
2. (Theorems 1, 2 and 4) If there is a set $W$ of covariates, nondescendants of $X$ and $Z$, satisfying the counterfactual independence condition (7) of the source, the natural direct and indirect effects are identified by adjusting for $W$.
3. In Markovian models in which the effect of $X$ on $Z$ is not confounded, these reduce to the mediation formulas
$$\mathrm{NDE}(x, x^*; Y) = \sum_z \bigl[E(Y \mid x, z) - E(Y \mid x^*, z)\bigr] P(z \mid x^*), \qquad \mathrm{NIE}(x, x^*; Y) = \sum_z E(Y \mid x^*, z)\bigl[P(z \mid x) - P(z \mid x^*)\bigr]$$
(equations (17) and (27) of the source): the direct effect is a weighted average of controlled direct effects with the mediator distributed as under $x^*$.

## Expansion

1. The model: a structural causal model with counterfactuals $Y_{xz}$, $Z_x$, and the definitions of total, controlled direct, natural direct and natural indirect effects.
2. The decomposition identities of Theorem 3 and the additive relation in linear models, where the indirect effect is the product of the treatment–mediator and mediator–outcome coefficients.
3. The identification conditions with a covariate set $W$, including the graphical criterion of Corollary 1.
4. The Markovian mediation formulas (17) and (27).

## Sources

- J. Pearl, Direct and indirect effects, in *Proc. 17th Conference on Uncertainty in Artificial Intelligence*, 2001, 411–420, Definitions 4–7, Theorems 1–4, equations (17) and (21)–(27). <https://arxiv.org/abs/1301.2300>
