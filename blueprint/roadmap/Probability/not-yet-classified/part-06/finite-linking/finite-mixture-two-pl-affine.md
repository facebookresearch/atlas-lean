# Finite-grid 2PL linking

Let $Z$ be a finite grid with latent law $\pi$ and ability map $\zeta : Z \to \mathbb R$, and let the 2PL model give independent item responses with $P(\text{item } i \text{ correct} \mid \theta) = \sigma(a_i(\theta - b_i))$, $\sigma$ the logistic function, over a finite set of items. Let $A \ne 0$ and $B$ be real; discriminations $a_i$ of any sign are allowed. Change the ability scale by $\theta \mapsto A\theta + B$, push the latent ability law forward accordingly, and transform items by $a_i \mapsto a_i/A$, $b_i \mapsto A b_i + B$. Then the response law of the latent mixture is unchanged, so is the expected total score, and that score equals

$$\sum_i \sum_{z \in Z} \pi(z)\,\sigma\bigl(a_i(\zeta(z) - b_i)\bigr).$$
