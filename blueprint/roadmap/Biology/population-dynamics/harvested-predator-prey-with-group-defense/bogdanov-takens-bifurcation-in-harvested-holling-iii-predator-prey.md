# Codimension-three Bogdanov–Takens bifurcation in a harvested predator–prey model with group defense

**Model.** After rescaling, prey $x$ and predators $y$ obey
$$\dot x = x\Big(1 - \frac{x}{K}\Big) - y\,p(x) - h, \qquad \dot y = y\big(-d + p(x)\big), \qquad p(x) = \frac{x^2}{a x^2 + b x + 1},$$
with carrying capacity $K$, constant prey harvesting $h > 0$, predator death rate $d$, and a generalized Holling type III response with $a > 0$, $b^2 < 4a$ (so $p > 0$ for $x > 0$). For $b < 0$, $p$ is non-monotone: predation efficiency declines at high prey density (group defense), which allows two coexistence equilibria $E_3$, $E_4$.

**Theorem.**
1. *(Dissipativity.)* If $K > 4h$, there are $\mathcal{H}, \mathcal{P}, \mathcal{R} > 0$ such that every orbit from the open first quadrant approaches a segment of the $x$-axis, exits through the positive $y$-axis (prey collapse), or enters $[\mathcal H, \mathcal P]\times[0, \mathcal R]$; orbits staying in the quadrant are bounded.
2. *(Types.)* When the two coexistence equilibria exist, $E_3$ is an antisaddle and $E_4$ a saddle.
3. *(Saddle-node.)* Let $b < 0$, $d = d_0 = 4/(4a - b^2)$, $K > -2/b$ and $0 < h < (4 + 2bK)/(-b^2K)$. Then $E_3$ and $E_4$ merge at $E_{34} = (x_{lr}, y_{lr})$ with $x_{lr} = -2/b$, the maximizer of $p$. If $K \ne K_0 = -4/b$, $E_{34}$ is a semi-hyperbolic saddle-node with nonzero eigenvalue $(bK + 4)/(bK)$.
4. *(Cusp of codimension 2 and 3.)* At $d = d_0$, $K = K_0$ and $0 < h < -1/b$, $E_{34}$ has a double zero eigenvalue; it is a cusp of codimension $2$ if $h \ne h_0 = (4a - 2b^2)/b^3$, and of codimension $3$ if $2a < b^2 < 4a$ and $h = h_0$ (then $h_0 > 0$).
5. *(Bogdanov–Takens of codimension 3.)* If $2a < b^2 < 4a$, then under the perturbation $(d - d_0, K - K_0, h - h_0) \approx 0$ the system undergoes a codimension-$3$ Bogdanov–Takens bifurcation near $E_{34}$.
6. *(Hopf.)* The weak focus $E_3$ has multiplicity at most two for $h > 0$, so at most two small limit cycles bifurcate from it, and it can be a codimension-$2$ generalized Hopf (Bautin) point.

## Depends on


## Expansion

Coexistence equilibria lie where $p(x) = d$; for $b < 0$ the hump of $p$ at $x = -2/b$ gives two roots, which collide when $d = \max p = d_0$. At the collision the Jacobian trace vanishes exactly when $K = K_0$, producing a nilpotent singularity. Near-identity transformations bring it to $\dot x = y$, $\dot y = x^2 + E x^3 y + O(|x,y|^5)$, and the vanishing of the second-order coefficient at $h = h_0$ raises the codimension; checking transversality of the parameter map $(d, K, h)$ to the universal unfolding gives the codimension-3 Bogdanov–Takens bifurcation, organizing saddle-node, Hopf, homoclinic and multiple limit-cycle curves. Hopf multiplicity is computed by a Liénard-system criterion on the focal values $B_i$.

## Sources

- W. El Khateeb, F. Akter, C. Kottegoda and M. M. Abou Hasan, "Dynamics of a Harvested Predator-Prey Model with a Generalized Holling Type III Response Capturing Group Defense", arXiv:2610.32306 (2026), Theorems 2.1, 3.1, 3.2, 3.4, 3.5, 3.7 and Proposition 3.3, <https://doi.org/10.48550/arXiv.2610.32306>.
