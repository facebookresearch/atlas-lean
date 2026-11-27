# Perron-eigenvector Lyapunov functions for the disease-free equilibrium

Write the infected compartments of a compartmental epidemic model as $x \in \mathbb{R}^n_{\ge 0}$ and the other variables as $y$, with $\dot x = (F - V)x - \tilde f(x, y)$, where $F \ge 0$ is the new-infection matrix and $V$ the transition matrix at the disease-free equilibrium, $V$ a nonsingular M-matrix ($V^{-1} \ge 0$), and $\tilde f(x, y) = (F - V)x - \mathcal F(x, y) + \mathcal V(x, y) \ge 0$ on a positively invariant set. Let $R_0 = \rho(FV^{-1}) = \rho(V^{-1}F)$ and let $w^T \ge 0$ be a left eigenvector of $V^{-1}F$ for the eigenvalue $R_0$. The method of Shuai and van den Driessche (2013), as applied by Niotis and Chudej (2025, Section 2), takes the linear Lyapunov function $Q(x) = w^T V^{-1} x$. The target is its derivative inequality: $\dot Q = w^T V^{-1}(F - V)x - w^T V^{-1}\tilde f = R_0\, w^T x - w^T x - w^T V^{-1}\tilde f$, so $\dot Q \le (R_0 - 1)\, w^T x \le 0$ when $R_0 \le 1$, because $w \ge 0$, $V^{-1} \ge 0$ and $\tilde f \ge 0$.

The inequality alone does not make a specified equilibrium of the full system attract the invariant set. Take $n = 1$, $F = 0$, $V = 1$, $\tilde f = 0$, $\dot x = -x$ and $\dot y = 0$ on the unit square: all the conditions above hold and $Q = x$ decreases, yet every point $(0, y)$ is an equilibrium and none of them attracts the whole square. Global asymptotic stability of the disease-free equilibrium on the invariant set when $R_0 < 1$ follows from LaSalle's invariance principle only under further hypotheses, which must be checked for the specified model, as Niotis and Chudej (2025, Section 2) do: the positively invariant set is compact (or its forward orbits are bounded), the disease-free equilibrium is stable, and the largest invariant subset of $\{\dot Q = 0\}$ is that single equilibrium.

## Depends on

- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)
- [Basic reproduction number of the next-generation matrix](../r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The model: the splitting into infected and uninfected variables, the hypotheses on $F$, $V$ and $\tilde f$, and the positively invariant region.
2. The left Perron eigenvector of $V^{-1}F$ via the [Perron–Frobenius theorem](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md), and the equality of the spectral radii of $FV^{-1}$ and $V^{-1}F$.
3. The derivative identity for $Q$ and the sign conclusion, which is the target.
4. As a separate statement, global asymptotic stability under the added hypotheses (compactness or bounded orbits, stability of the disease-free equilibrium): [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md) and the identification of the largest invariant set in $\{\dot Q = 0\}$ with the disease-free equilibrium, which is where model-specific hypotheses enter (including irreducibility of $V^{-1}F$ for the case $R_0 = 1$).
5. The graph-theoretic Lyapunov functions for endemic equilibria in the same source, as a separate statement.

## Sources

- A. Niotis and K. Chudej, Mathematical analysis of a compartment model, SNE Simul. Notes Eur. 35 (2025), 17–24, Section 2 (stability of the disease-free equilibrium). <https://doi.org/10.11128/sne.35.tn.10723>
- Original result: Z. Shuai and P. van den Driessche, Global stability of infectious disease models using Lyapunov functions, SIAM J. Appl. Math. 73 (2013), 1513–1532. <https://doi.org/10.1137/120876642> The Lyapunov function $w^T V^{-1}x$ follows Niotis and Chudej, who apply it following Shuai and van den Driessche.
