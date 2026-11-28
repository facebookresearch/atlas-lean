# Energy balance of the circulatory model

Let $q \in \mathbb{R}$, $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$, and let $z : \mathbb{R} \to \mathbb{R}^2$ be $C^2$. Write

$$R(t) = z''(t) + 2z'(t) + z(t) - q\,J z(t)$$

for the model residual and $E(t) = \tfrac12\big(z'(t)\cdot z'(t) + z(t)\cdot z(t)\big)$ for the energy. Then for every $t$, $E$ is differentiable at $t$ with

$$E'(t) = R(t)\cdot z'(t) - 2\,z'(t)\cdot z'(t) + \big(q\,J z(t)\big)\cdot z'(t).$$
