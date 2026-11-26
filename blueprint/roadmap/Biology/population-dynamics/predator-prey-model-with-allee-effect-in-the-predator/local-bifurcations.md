# Local bifurcations of the predator–prey model with predator Allee effect

For the [predator–prey model with an Allee effect in the predator](equilibria-and-stability.md),

$$F_1 = x(1-x) - \frac{xy}{\beta+x}, \qquad F_2 = \frac{\alpha xy}{\beta+x}h(y) - my,$$

with $h$ satisfying (A1)–(A5), the following local bifurcations of interior equilibria occur.

**Saddle-node.** Two interior equilibria collide when the nullclines are tangent, $f^1_xf^2_y - f^1_yf^2_x = 0$ (so $\det J = 0$). With $m$ as parameter at $m = m_{SN}$ and equilibrium $\bar E = (\bar x, \bar y)$, the right and left null vectors of $J(\bar E)$ are $v = (1,\ 1-\beta-2\bar x)^\top$ and $w = (\alpha\bar yh'(\bar y),\ 1)^\top$, and the transversality conditions hold for every admissible $h$: $w^\top F_m(\bar E) \ne 0$ and $w^\top D^2F(\bar E)(v,v) < 0$ (using $h'' < 0$). Hence the saddle-node is generic and creates the saddle $E_2^*$ and the node/focus $E_1^*$.

**Hopf.** $E_1^*$ changes stability through a Hopf bifurcation where $\operatorname{tr}J(E_1^*) = 0$ with $\det J(E_1^*) > 0$ (parameter $\beta$).

**Bautin (Proposition 2).** The model undergoes a generalized Hopf bifurcation at $(\beta_{GH}, m_{GH})$ around $\hat E$ when $\det J(\hat E) > 0$, $\operatorname{tr}J(\hat E) = 0$ and the first Lyapunov number $l(\hat E) = 0$.

**Bogdanov–Takens (Proposition 3).** With $(\beta, m)$ as parameters, the model undergoes a Bogdanov–Takens bifurcation at $\bar E$ when $\operatorname{tr}J(\bar E) = 0$ and $\det J(\bar E) = 0$ (the Jacobian is similar to $\begin{pmatrix}0&1\\0&0\end{pmatrix}$); it can be of codimension $2$ or (with an extra degeneracy) codimension $3$ of the double-equilibrium type. A cusp-type codimension-3 point, and any codimension-4 Bogdanov–Takens point, are impossible because the model has no triple equilibrium.

## Depends on

- [Predator–prey model with an Allee effect in the predator: equilibria and stability](equilibria-and-stability.md)

## Expansion

Sotomayor's theorem gives the saddle-node from $w^\top F_m \ne 0$ and $w^\top D^2F(v,v) \ne 0$. Because at most two interior equilibria exist (convex predator nullcline against a concave prey parabola), the Jacobian at a degenerate equilibrium has a double, never triple, zero structure, which bounds the codimension of Bogdanov–Takens points. The Bautin point separates sub- and supercritical Hopf branches, producing coexisting stable and unstable limit cycles nearby.

## Sources

- Deeptajyoti Sen, Saktipada Ghorai and Malay Banerjee, "Bifurcation analysis of the predator–prey model with the Allee effect in the predator", Journal of Mathematical Biology (2021), <https://doi.org/10.1007/s00285-021-01707-x> (PMC8718388). Section 4.1–4.4, Eqs. (15)–(16), Propositions 2 and 3 (proofs in the supplementary material).
