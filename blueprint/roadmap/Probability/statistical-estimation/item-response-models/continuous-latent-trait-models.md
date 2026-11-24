# Item response models with a continuous latent trait

An item response model with a continuous latent trait for $J$ binary items consists of a probability measure $G$ on $\mathbb R$, the ability distribution, and measurable item response functions $P_j : \mathbb R \to [0, 1]$, $j = 1, \dots, J$. A person's ability $\Theta$ has law $G$, and given $\Theta = \theta$ the responses $X_1, \dots, X_J \in \{0, 1\}$ are independent (local independence) with $\mathbb P(X_j = 1 \mid \Theta = \theta) = P_j(\theta)$. The response pattern $x \in \{0, 1\}^J$ then has probability

$$\mathbb P(X = x) = \int_{\mathbb R} \prod_{j=1}^J P_j(\theta)^{x_j} \bigl(1 - P_j(\theta)\bigr)^{1 - x_j}\, G(d\theta),$$

and the conditional law of $X$ given $\Theta$ is given by the Markov kernel $\theta \mapsto \bigotimes_j \mathrm{Bernoulli}(P_j(\theta))$. The two-parameter logistic model takes $P_j(\theta) = \bigl(1 + e^{-a_j(\theta - b_j)}\bigr)^{-1}$ with discriminations $a_j > 0$ and difficulties $b_j$, and the Rasch model is the case $a_j = 1$. When $G$ is supported on finitely many points the model is a finite latent-class model whose ability law is a probability mass function on a grid.

## Sources

- F. M. Lord, *Applications of Item Response Theory to Practical Testing Problems*, Lawrence Erlbaum, 1980
- G. Rasch, *Probabilistic Models for Some Intelligence and Attainment Tests*, Danish Institute for Educational Research, 1960
