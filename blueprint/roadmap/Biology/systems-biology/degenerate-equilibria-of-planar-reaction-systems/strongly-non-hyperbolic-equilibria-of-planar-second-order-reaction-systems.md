# Strongly non-hyperbolic equilibria of planar second-order reaction systems

**Chemical quadratic systems.** A network of reactions $\alpha_iX+\beta_iY\to\gamma_iX+\delta_iY$ with $\alpha_i+\beta_i\le2$ (at most bimolecular) under mass action gives
$$\dot x=\sum_{i+j\le2}a_{i,j}x^iy^j,\qquad \dot y=\sum_{i+j\le2}b_{i,j}x^iy^j .$$
A quadratic planar system arises from some such network if and only if there are no negative cross terms: $a_{0,0},a_{0,1},a_{0,2}\ge0$ and $b_{0,0},b_{1,0},b_{2,0}\ge0$ (a species cannot be consumed by a reaction in which it does not appear). An equilibrium is **strongly non-hyperbolic** if the Jacobian there is the zero matrix; then the local phase portrait is determined by the quadratic part and is a union of elliptic, hyperbolic and parabolic sectors. Lyagina classified homogeneous planar quadratic systems into sixteen geometric equivalence classes.

**At the origin.** With the equilibrium at $[0,0]$ the system is homogeneous quadratic with constraints $a_{0,2}\ge0$, $b_{2,0}\ge0$ only, and all sixteen Lyagina classes are realized by chemical systems, including elliptic sectors. Example: $2X\to3X$, $X+Y\xrightarrow{3}2Y$, $2Y\to Y$ gives $\dot x=x^2-3xy$, $\dot y=3xy-y^2$ with first integral $xy=c\,(x+y)^4$, so every trajectory in the open positive quadrant is homoclinic to the origin.

**Theorem (positive equilibria).** Rescale a positive strongly non-hyperbolic equilibrium to $[1,1]$. The linear and constant coefficients are then determined by the six quadratic ones ($a_{1,0}=-2a_{2,0}-a_{1,1}$, $a_{0,0}=a_{2,0}+a_{1,1}+a_{0,2}$, and similarly for $b$), and the chemical constraints become
$$a_{2,0}+a_{1,1}+a_{0,2}\ge0,\quad b_{2,0}+b_{1,1}+b_{0,2}\ge0,\quad -a_{1,1}\ge2a_{0,2}\ge0,\quad -b_{1,1}\ge2b_{2,0}\ge0 .$$
Of Lyagina's sixteen classes, exactly nine are realized by planar second-order chemical systems at a positive strongly non-hyperbolic equilibrium. In particular **no elliptic sector** can occur there. Every realizable class has a representative with only 8 to 10 non-zero terms.

## Depends on

- [Chemical reaction network theory](../chemical-reaction-network-theory/README.md)

## Expansion

Near the degenerate point the dynamics are governed by the invariant lines through it, $y-1=\eta(x-1)$, whose slopes solve a cubic $\sigma_3\eta^3-\sigma_2\eta^2+\sigma_1\eta-\sigma_0=0$ with coefficients built from the quadratic part; the number and multiplicity of real roots (three, one, a triple root, a double plus a simple root, or the case $\sigma_3=0$ where $x=1$ is invariant) organize the sector structure. Rewriting the chemical inequalities in terms of the $\sigma_k$ and two further parameters produces a **chemical triangle** of admissible parameters. For each root configuration one decides when the triangle is non-empty, which shows that it always lies on one side of an undefined-derivative line. The configurations producing elliptic sectors are exactly those for which the triangle is empty. The positive-equilibrium constraints remove classes because the coefficients must keep consistent signs on both sides of the equilibrium, a restriction that disappears on the boundary of the quadrant.

## Sources

- N. Yeung, R. Erban, "Classification of strongly non-hyperbolic critical points of planar second-order chemical reaction systems", arXiv:2610.06130 (2026), Section 1 (chemical sign conditions), Section 2 (origin, Example 2.1), Section 3 (Lemmas 1-9) and Section 4 (summary table of realizable classes), <https://doi.org/10.48550/arXiv.2610.06130>.
