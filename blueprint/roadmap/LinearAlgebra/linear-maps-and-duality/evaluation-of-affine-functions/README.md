# Evaluation of an affine function at two points

Let $F$ be a field and let $\theta \ne \theta'$ be elements of $F$. The map $(a, b) \mapsto (a\theta + b,\ a\theta' + b)$, sending the slope and intercept of the affine function $x \mapsto ax + b$ to its values at $\theta$ and $\theta'$, is a linear isomorphism $F^2 \to F^2$, with inverse $(y, y') \mapsto \bigl(\frac{y - y'}{\theta - \theta'},\ y - \frac{y - y'}{\theta - \theta'}\, \theta\bigr)$.

## Idea

An affine function is determined by its values at two distinct points, and every pair of values occurs: this is linear interpolation in degree one. The matrix of the map is the $2 \times 2$ Vandermonde matrix $\begin{pmatrix} \theta & 1 \\ \theta' & 1 \end{pmatrix}$, whose determinant $\theta - \theta'$ is nonzero exactly when the points are distinct, and the inverse is the formula for the slope and intercept of the line through two points. The same statement in degree $d$, with $d + 1$ points, is Lagrange interpolation.

## Statements

- [Evaluation of an affine function at two points](affine-evaluation.md)
