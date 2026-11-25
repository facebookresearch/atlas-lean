# Rasch model

For item difficulties $b_i \in \mathbb R$, $i \in I$, and an ability $\theta \in \mathbb R$, the Rasch model is the [law of locally independent binary responses](local-independence-response-law.md) with success probabilities $q_i = \sigma(\theta - b_i)$, where $\sigma(t) = 1 / (1 + e^{-t})$ is the logistic function.

## Sources

- P. Mair and R. Hatzinger, "Extended Rasch modeling: the eRm package for the application of IRT models in R", *Journal of Statistical Software* 20(9), 2007, Section 3.1 (the Rasch model with local independence)
- J. P. Weeks, "plink: An R package for linking mixed-format tests using IRT-based methods", *Journal of Statistical Software* 35(12), 2010, Section 2, Equation (1) (dichotomous models, here with scaling constant $D = 1$ and no lower asymptote)
