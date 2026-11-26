# Local bifurcations of the predator–prey model with predator Allee effect

For the [predator–prey model with an Allee effect in the predator](equilibria-and-stability.md),

$$F_1 = x(1-x) - \frac{xy}{\beta+x}, \qquad F_2 = \frac{\alpha xy}{\beta+x}h(y) - my,$$

with $h$ satisfying (A1)–(A5), the following local bifurcations of interior equilibria occur.

**Saddle-node.** Two interior equilibria collide when the nullclines are tangent, $f^1_xf^2_y - f^1_yf^2_x = 0$ (so $\det J = 0$). With $m$ as parameter at $m = m_{SN}$ and equilibrium $\bar E = (\bar x, \bar y)$, the right and left null vectors of $J(\bar E)$ are $v = (1,\ 1-\beta-2\bar x)^\top$ and $w = (\alpha\bar yh'(\bar y),\ 1)^\top$, and the transversality conditions hold for every admissible $h$: $w^\top F_m(\bar E) = -1 \ne 0$ and $w^\top D^2F(\bar E)(v,v) < 0$ (using $h'' < 0$). If moreover $0$ is a simple eigenvalue of $J(\bar E)$, i.e. $\operatorname{tr}J(\bar E) \ne 0$, Sotomayor's theorem gives a generic saddle-node, which creates the saddle $E_2^*$ and the node/focus $E_1^*$. Simplicity is a real restriction: for $h(y) = y/(1/9 + y)$ and $(\alpha, \beta, m) = (32/9, 1/3, 16/9)$, the point $(2/3, 1/3)$ is an equilibrium at which both the trace and the determinant vanish, a Bogdanov–Takens point rather than an ordinary fold.

**Hopf.** Take $\beta$ as parameter along a branch of equilibria $E_1^*(\beta)$ and let $\beta_H$ be a value with $\operatorname{tr}J(E_1^*(\beta_H)) = 0$ and $\det J(E_1^*(\beta_H)) > 0$. If the transversality condition $\frac{d}{d\beta}\operatorname{Re}\lambda(\beta)\big|_{\beta_H} \ne 0$ holds for the complex pair $\lambda(\beta)$, $E_1^*$ changes linear stability through a Hopf bifurcation at $\beta_H$; a nonzero first Lyapunov coefficient $l_1$ makes it nondegenerate, supercritical if $l_1 < 0$ and subcritical if $l_1 > 0$. The source gives an explicit expression for the transversality derivative and checks numerically that it is nonzero at the Hopf threshold for the Monod, Ivlev and hyperbolic-tangent forms of $h$; zero trace with positive determinant alone does not establish the crossing.

**Bautin (Proposition 2).** Suppose that at $(\beta_{GH}, m_{GH})$ the interior equilibrium $\hat E$ has $\det J(\hat E) > 0$, $\operatorname{tr}J(\hat E) = 0$ and first Lyapunov number $l_1(\hat E) = 0$, that the second Lyapunov coefficient $l_2(\hat E) \ne 0$, and that the map $(\beta, m) \mapsto (\operatorname{Re}\lambda, l_1)$ has rank two there. Then the model undergoes a generic generalized Hopf (Bautin) bifurcation at $(\beta_{GH}, m_{GH})$. The source's Proposition 2 lists only the first three conditions; the two nondegeneracy conditions are what make the unfolding generic, and the source exhibits Bautin points numerically for its three forms of $h$ (Section 5).

**Bogdanov–Takens (Proposition 3).** With $(\beta, m)$ as parameters, an interior equilibrium $\bar E$ with $\operatorname{tr}J(\bar E) = 0$ and $\det J(\bar E) = 0$, at which $J(\bar E) \ne 0$ is similar to $\begin{pmatrix}0&1\\0&0\end{pmatrix}$, is a Bogdanov–Takens point; the bifurcation is generic of codimension $2$ when its two quadratic normal-form coefficients are nonzero and the unfolding by $(\beta, m)$ is regular (proof in the source's supplementary material); it can be of codimension $2$ or (with an extra degeneracy) codimension $3$ of the double-equilibrium type. A cusp-type codimension-3 point, and any codimension-4 Bogdanov–Takens point, are impossible because the model has no triple equilibrium.

## Depends on

- [Predator–prey model with an Allee effect in the predator: equilibria and stability](equilibria-and-stability.md)

## Expansion

Sotomayor's theorem gives the saddle-node from a simple zero eigenvalue together with $w^\top F_m \ne 0$ and $w^\top D^2F(v,v) \ne 0$. Because at most two interior equilibria exist (convex predator nullcline against a concave prey parabola), the Jacobian at a degenerate equilibrium has a double, never triple, zero structure, which bounds the codimension of Bogdanov–Takens points. The Bautin point separates sub- and supercritical Hopf branches, producing coexisting stable and unstable limit cycles nearby.

## Sources

- Deeptajyoti Sen, Saktipada Ghorai, Malay Banerjee and Andrew Morozov, "Bifurcation analysis of the predator–prey model with the Allee effect in the predator", Journal of Mathematical Biology 84 (2022), article 7, <https://doi.org/10.1007/s00285-021-01707-x> (PMC8718388). Section 4.1–4.4, Eqs. (15)–(16), Propositions 2 and 3 (proofs in the supplementary material).
