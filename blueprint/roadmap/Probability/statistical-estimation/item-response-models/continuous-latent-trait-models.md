# Item response models with a continuous latent trait

An item response model with a continuous latent trait for a finite set $I$ of binary items consists of a probability measure $G$ on $\mathbb R$, the ability distribution, and measurable item response functions $P_i : \mathbb R \to [0, 1]$, $i \in I$. A person's ability $\Theta$ has law $G$, and given $\Theta = \theta$ the responses have the [law of locally independent binary responses](local-independence-response-law.md) with success probabilities $P_i(\theta)$. The response pattern $x : I \to \{0, 1\}$ then has marginal probability

$$\mathbb P(X = x) = \int_{\mathbb R} \prod_{i \in I} \pi_i(\theta, x_i)\, G(d\theta), \qquad \pi_i(\theta, 1) = P_i(\theta), \quad \pi_i(\theta, 0) = 1 - P_i(\theta).$$

The [two-parameter logistic model](two-parameter-logistic-model.md) and the [Rasch model](rasch-model-response-law.md) supply the item response functions of the most common such models. When $G$ is supported on finitely many points the model is a finite latent-class model.

## Depends on

- [Law of locally independent binary responses](local-independence-response-law.md)

## Sources

- F. M. Lord, *Applications of Item Response Theory to Practical Testing Problems*, Lawrence Erlbaum, 1980
- G. Rasch, *Probabilistic Models for Some Intelligence and Attainment Tests*, Danish Institute for Educational Research, 1960
