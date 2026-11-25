# Christoffel symbols of a metric on $\mathbb{R}^n$

Let $g : \mathbb{R}^n \to \mathbb{R}^{n \times n}$ be a matrix-valued function, written $g_{ij}(x)$, and let $g^{kl}(x)$ denote the entries of the inverse matrix $g(x)^{-1}$. The Christoffel symbols of $g$ at $x$ are

$$\Gamma^k_{ij}(x) = \frac{1}{2} \sum_{l=1}^{n} g^{kl}(x) \bigl( \partial_i g_{jl}(x) + \partial_j g_{il}(x) - \partial_l g_{ij}(x) \bigr),$$

with $\partial_i$ the partial derivative (taken to be $0$ where the function is not differentiable). For a smooth positive definite $g$ on an open set these are the coefficients of the Levi-Civita connection. The inverse is the matrix inverse with the convention $g(x)^{-1} = 0$ when $g(x)$ is singular.
