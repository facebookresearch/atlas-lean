# Moments of a latent-mixture binary model

Let $Z$ (latent states) and the item set be finite, $\pi$ a probability distribution on $Z$, and $q_{z,i} \in [0, 1]$. Let the observed binary vector $x$ be drawn by choosing $z \sim \pi$ and then setting the items independently with $P(x_i = 1 \mid z) = q_{z,i}$. Then:
- $E[x_i] = \sum_z \pi(z)\,q_{z,i}$ for every item $i$;
- $E[x_i x_j] = \sum_z \pi(z)\,q_{z,i}q_{z,j}$ for $i \ne j$;
- for $i \ne j$, $\operatorname{Cov}(x_i, x_j)$ equals the covariance of $z \mapsto q_{z,i}$ and $z \mapsto q_{z,j}$ under $\pi$.
