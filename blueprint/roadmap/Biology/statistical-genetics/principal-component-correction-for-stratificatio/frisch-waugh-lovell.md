# Frisch–Waugh–Lovell theorem, uniqueness

Let $V \subseteq \mathbb{R}^N$ be a linear subspace and let $y, g \in \mathbb{R}^N$ with $r_V(g) \ne 0$, where $r_V$ is the [residual](adjusted.md). Let $c \in V$ and $\beta \in \mathbb{R}$ be such that $y - c - \beta g$ is orthogonal to $V + \operatorname{span}\{g\}$. Then

- $\beta = \dfrac{\langle r_V(g), r_V(y) \rangle}{\|r_V(g)\|^2}$;
- $y - c - \beta g = r_V(y) - \beta\, r_V(g)$.

So the coefficient of $g$ in the least-squares regression of $y$ on $V$ and $g$ is the coefficient of the regression of the residualized $y$ on the residualized $g$, with the same residual.
