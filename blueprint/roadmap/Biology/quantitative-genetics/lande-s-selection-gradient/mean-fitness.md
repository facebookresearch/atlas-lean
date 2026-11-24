# Mean fitness of a normally distributed trait

For a fitness function $W : \mathbb{R} \to \mathbb{R}$, a trait mean $\mu \in \mathbb{R}$ and a variance $v \ge 0$, the mean fitness is

$$\bar w(\mu) = \int W(z) \, dN(\mu, v)(z),$$

with the convention that the integral of a non-integrable function is $0$ ($N(\mu, 0)$ is the point mass at $\mu$).
