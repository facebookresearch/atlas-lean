# Successor of a boundary dart

Let $K \subseteq \mathbb{Z}^2$ and let $e$ be a dart of the square lattice with tail $t$, head $h$ and direction $u = h - t$. Let $\rho(a, b) = (-b, a)$ be the counterclockwise quarter-turn rotation and $r = -\rho(u)$ the direction $u$ rotated clockwise by a quarter turn. The successor $\sigma_K(e)$ of $e$ along the boundary of $K$ is the dart

- from $h + r$ to $h$ (direction $\rho(u)$), if $h + r \in K$;
- from $t + r$ to $h + r$ (direction $u$), if $h + r \notin K$ and $t + r \in K$;
- from $t$ to $t + r$ (direction $r$), otherwise.

The definition applies to every dart; for a boundary dart of $K$ (tail in $K$, head outside $K$) the successor is again a boundary dart.
