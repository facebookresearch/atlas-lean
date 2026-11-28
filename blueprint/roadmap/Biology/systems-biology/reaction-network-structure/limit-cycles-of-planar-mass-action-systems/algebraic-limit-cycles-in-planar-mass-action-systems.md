# Algebraic limit cycles in planar mass-action systems

**Setting.** A planar polynomial ODE system $\dot x = f(x,y)$, $\dot y = g(x,y)$ is realisable as a chemical reaction network under mass-action kinetics when every monomial with negative coefficient in $f$ is divisible by $x$ and every such monomial in $g$ is divisible by $y$ (no negative cross-effects). A limit cycle is *algebraic* if it is contained in the zero set of a polynomial. $W^a(n)$ denotes the maximal number of algebraic limit cycles of planar reversible mass-action systems of order at most $n$.

**Theorem (construction).** Let $h:\mathbb{R}^2\to\mathbb{R}$ be a polynomial of degree $n_h$ whose zero set contains $N$ ovals in the open positive quadrant, and suppose $\nabla h\ne 0$ on $\{h=0\}$. Then for every $\varepsilon>0$ the system

$$\dot x = -\,xy\,h\,\partial_x h - \varepsilon\,xy\,\partial_y h, \qquad \dot y = -\,xy\,h\,\partial_y h + \varepsilon\,xy\,\partial_x h$$

has degree $2n_h+1$, is realisable as a mass-action reaction network, and has $N$ stable algebraic limit cycles, namely the $N$ ovals of $h=0$.

**Theorem (many cycles).** For every $N\in\mathbb{N}$ there is a reversible chemical reaction system of order $4N+2$ with $N$ algebraic limit cycles; hence $W^a(4N+2)\ge N$.

## Expansion

Along $h=0$ the vector field reduces to $\varepsilon\,xy\,(-\partial_y h, \partial_x h)$, which is tangent to the curve and nonvanishing in the positive quadrant, so each oval is a periodic orbit. Off the curve, $\frac{d}{dt}h = -xy\,h\,|\nabla h|^2$ drives $h$ towards zero, making each oval attracting. Multiplying by $xy$ removes negative cross-effects, so the system is a mass-action network. The general version replaces the gradient-descent term by any polynomial field transverse to the ovals, with the sign of the transversality expression deciding stability.

## Sources

- G. Craciun, R. Erban, "Planar chemical reaction systems with algebraic and non-algebraic limit cycles", *Journal of Mathematical Biology* 90(6) (2025), 64, Theorems 1–3, <https://doi.org/10.1007/s00285-025-02221-0> (preprint arXiv:2406.05057).
