# Aizenman–Barsky critical bound $M(\beta_c, h) \ge c\sqrt{h}$

Let $M : \mathbb{R}^2 \to \mathbb{R}$ and let $J > 0$ and $\beta_c > 0$ be real numbers. Derivatives are read as $0$ at points where the function is not differentiable. Assume:

- $M$ satisfies the [Aizenman–Barsky inequality](aizenman-barsky-inequality.md) $\partial_\beta M(\beta, h) \le J\, M(\beta, h)\, \partial_h M(\beta, h)$ for all real $\beta, h$;
- $h \mapsto M(\beta_c, h)$ is differentiable with $\partial_h M(\beta_c, h) \ge 0$ at every $h \ge 0$;
- $M(\beta_c, h) \ge 0$ for all $h$, and $M(\beta_c, 0) = 0$;
- $1 - M(\beta_c, h) \le \beta_c\, \partial_\beta M(\beta_c, h)$ for every $h \ge 0$.

Then there is $c > 0$ such that

$$M(\beta_c, h) \ge c \sqrt{h} \quad \text{for all } 0 < h \le \beta_c J / 4.$$

## Sources

- Michael Aizenman and David J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math. Phys. 108
  (1987), no. 3, 489–526, DOI 10.1007/bf01212322.
