# Two-parameter logistic model

For item discriminations $a_i \in \mathbb R$, item difficulties $b_i \in \mathbb R$, $i \in I$, and an ability $\theta \in \mathbb R$, the two-parameter logistic model is the [law of locally independent binary responses](local-independence-response-law.md) with success probabilities $q_i = \sigma(a_i (\theta - b_i))$, where $\sigma(t) = 1 / (1 + e^{-t})$ is the logistic function. This is the logistic metric with scaling constant $1$.

## Sources

- J. P. Weeks, "plink: An R package for linking mixed-format tests using IRT-based methods", *Journal of Statistical Software* 35(12), 2010, Section 2, Equation (1) (dichotomous models, here with scaling constant $D = 1$ and no lower asymptote)
