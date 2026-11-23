# Killing fields are those with vanishing Lie derivative of the metric

Let $M$ be a smooth
Riemannian manifold with metric $g = \langle \cdot, \cdot \rangle$. A vector field $X$ on $M$ is
a Killing vector field if and only if $X$ is smooth and, for every point $x \in M$ and all vector
fields $Y$ and $Z$ on $M$ that are differentiable at $x$,

$$X_x \langle Y, Z \rangle - \langle [X, Y]_x, Z_x \rangle - \langle Y_x, [X, Z]_x \rangle = 0,$$

where $X_x \langle Y, Z \rangle$ is the derivative at $x$ of the function
$y \mapsto \langle Y_y, Z_y \rangle$ in the direction $X_x$, and $[X, Y]$ is the Lie bracket.
The left-hand side is $(L_X g)(Y, Z)$ at $x$, where $L_X g$ is the Lie derivative of $g$ along
$X$.
