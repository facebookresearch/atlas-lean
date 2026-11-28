# Hayman's function b(r)

For $f : \mathbb{C} \to \mathbb{C}$ let $\theta g(r) = r \, g'(r)$ and

$$
b(r) = \theta\bigl(\theta \log M(\cdot, f)\bigr)(r), \qquad \text{that is } b(r) = \Bigl(r \frac{d}{dr}\Bigr)^2 \log M(r, f),
$$

with $M(r, f)$ the [maximum modulus](max-modulus.md) and $\log 0 = 0$.

Both derivatives are total: at a radius where the function being differentiated has no derivative, its derivative is taken to be $0$. So $b(r)$ is defined for every real $r$. Wherever $\log M(\cdot, f)$ is twice differentiable on a neighbourhood of $r$, $b(r)$ is the classical value; at the exceptional radii, where $\log M(r, f)$ or $r \frac{d}{dr} \log M(r, f)$ is not differentiable (for a transcendental entire function $\log M(r, f)$ is a convex function of $\log r$, differentiable except at countably many radii), $b(r)$ is the value produced by this convention, and those radii are not excluded from limits such as $\limsup_{r \to \infty} b(r)$.
