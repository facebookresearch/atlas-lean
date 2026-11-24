# Linking two-parameter logistic scales and test scores

(Finite latent mixture.) Let $Z$ be a finite grid with probability mass function $\pi$, $\zeta : Z \to \mathbb{R}$ an ability map, and $f(\theta) = A\theta + B$ with $A > 0$. For items $j$ in a finite index set, transform item parameters by $a_j' = a_j/A$, $b_j' = Ab_j + B$. Since each item's response law is unchanged under this change of ability scale, the law of the response pattern under the mixture $\sum_z \pi(z)\prod_j P(Y_j \mid \zeta(z))$ equals the law under the pushed abilities $f \circ \zeta$ with the transformed items, and so does the law of the total score $\sum_j Y_j$.

(Linear score map.) For $\sigma_X, \sigma_Y > 0$, the map $\ell(x) = \mu_Y + (\sigma_Y/\sigma_X)(x - \mu_X)$ has inverse $y \mapsto \mu_X + (\sigma_X/\sigma_Y)(y - \mu_Y)$, and if $X$ has mean $\mu_X$ and standard deviation $\sigma_X$ then $\ell(X)$ has mean $\mu_Y$ and standard deviation $\sigma_Y$.

(Equipercentile map.) If probability measures $\mu, \nu$ on $\mathbb{R}$ have continuous, strictly increasing distribution functions $F, G$, then $e = G^{-1} \circ F$ pushes $\mu$ forward to $\nu$ and $G^{-1} \circ F$ and $F^{-1} \circ G$ are mutually inverse. For distributions with atoms these maps need not be inverse to each other, with the quantile $G^{-1}(u) = \inf\{x : G(x) \ge u\}$ for $0 < u < 1$: for $\mu$ uniform on $\{0, 1\}$ and $\nu$ uniform on $\{0, 1, 2\}$, $G^{-1}(F(0)) = G^{-1}(1/2) = 1$ and $F^{-1}(G(1)) = F^{-1}(2/3) = 1$, so the round trip sends $0$ to $1$.

These are relations between model coordinates and laws, not claims that scores on different forms are interchangeable. Mixing over an arbitrary latent ability distribution, rather than a finite grid, is outside this statement.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Invariance of the two-parameter logistic response law under $\theta \mapsto A\theta + B$, $a_j \mapsto a_j/A$, $b_j \mapsto Ab_j + B$ for $A > 0$.
- Probability integral transform and quantile transform for continuous strictly increasing distribution functions.
