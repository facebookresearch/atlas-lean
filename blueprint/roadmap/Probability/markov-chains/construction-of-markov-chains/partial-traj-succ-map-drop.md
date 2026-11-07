# One-step shift of a Markov partial trajectory

Let $\kappa$ be a Markov kernel on a
measurable space $S$, let $a, b \in \mathbb{N}$ and let $z = (z_0, \dots, z_{a+b})$ be a history
in $S^{\{0, \dots, a+b\}}$. Let $\mu_z$ be the one-step partial trajectory of the lifted kernel
of $\kappa$ from time $a + b$ to time $a + b + 1$ started at $z$, that is, the law of
$(z_0, \dots, z_{a+b}, X)$ where $X$ has law $\kappa(z_{a+b})$. Then the image of $\mu_z$ under
the map $(y_0, \dots, y_{a+b+1}) \mapsto (y_a, \dots, y_{a+b+1})$ that drops the first $a$
coordinates equals the one-step partial trajectory of the lifted kernel from time $b$ to time
$b + 1$ started at $(z_a, \dots, z_{a+b})$, that is, the law of $(z_a, \dots, z_{a+b}, X')$ where
$X'$ has law $\kappa(z_{a+b})$.
