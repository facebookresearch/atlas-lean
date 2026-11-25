# Sheppard's formula

Let $-1 < \rho < 1$, and let $(X_1, X_2)$ be a standard bivariate normal vector with correlation $\rho$: its law is the Gaussian measure on $\mathbb{R}^2$ with mean $0$ and covariance matrix with diagonal entries $1$ and off-diagonal entries $\rho$. Then the probability that both coordinates are positive is $P(X_1 > 0,\ X_2 > 0) = \frac{1}{4} + \frac{\arcsin \rho}{2\pi}$.

## Idea

The formula turns a correlation into an orthant probability; for $\rho = 0$ it gives $1/4$, and as $\rho \to 1$ it tends to $1/2$. A geometric proof: write $X_1 = \langle u, r\rangle$ and $X_2 = \langle v, r\rangle$, with $r$ a standard Gaussian vector in the plane and $u, v$ unit vectors with $\langle u, v\rangle = \rho$. The two vectors have the same characteristic function, hence the same law. The direction of $r$ is uniform, so the signs of $X_1$ and $X_2$ differ with probability $\arccos(\rho)/\pi$, the angle between $u$ and $v$ divided by $\pi$. The symmetry $r \mapsto -r$ makes the two agreeing sign patterns equally likely. Each therefore has probability $\frac12(1 - \arccos(\rho)/\pi)$, which equals the formula. The same computation drives the random-hyperplane rounding of Goemans and Williamson.

## Statements

- [Sheppard's formula (Gaussian arcsine law)](sheppard-quadrant-probability-arcsine.md)
- [Characteristic function of a pair of inner products](char-fun-map-inner-pair.md): lemma used in the proof of the main statement
- [One-dimensional marginal of the standard Gaussian](map-inner-std-gaussian.md): lemma used for the hyperplane form
- [Two-dimensional marginal of the standard Gaussian](map-inner-pair-std-gaussian.md): lemma used for the hyperplane form
- [Sign-disagreement sets are measurable](measurable-set-sign-ne.md): lemma used for the hyperplane form
- [Hyperplanes through the origin are null for the standard Gaussian](std-gaussian-inner-eq-zero.md): lemma used for the quadrant form
- [The planar wedge probability](gaussian-real-prod-wedge.md): lemma used for the hyperplane form
- [A random hyperplane separates two unit vectors with probability angle over π](std-gaussian-sign-ne.md): hyperplane-rounding form: separation probability angle/π
- [Quadrant probability for two directions](std-gaussian-pos-pos.md): quadrant probability for two directions

## Sources

- W. F. Sheppard, "On the application of the theory of error to cases of normal distribution and normal correlation", *Philosophical Transactions of the Royal Society of London, Series A* (1899).
