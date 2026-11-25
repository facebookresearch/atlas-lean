# Threshold theorem, stability half, conditional decay form

Let $\iota$ (the infected compartments) and $\kappa$ (the others) be finite sets, and let
$f \colon \mathbb{R}^{\iota \sqcup \kappa} \to \mathbb{R}^{\iota \sqcup \kappa}$ have an equilibrium
$f(x_0) = 0$ at which it is differentiable with derivative

$$J = \begin{pmatrix} F - V & 0 \\ C & D \end{pmatrix},$$

the block form of van den Driessche and Watmough (2002, Lemma 1), where $F$ is entrywise nonnegative,
$V$ is a nonsingular M-matrix (nonpositive off-diagonal entries, all complex eigenvalues with positive
real part) and every complex eigenvalue of $D$ has negative real part. If the
[basic reproduction number](r0.md) satisfies $R_0 = \rho(F V^{-1}) < 1$, then there are
$\delta, K, \alpha > 0$ such that every $x \colon \mathbb{R} \to \mathbb{R}^{\iota \sqcup \kappa}$ with
$x'(t) = f(x(t))$ for all $t \ge 0$ and $\|x(0) - x_0\| < \delta$ satisfies

$$\|x(t) - x_0\| \le K e^{-\alpha t} \|x(0) - x_0\| \quad \text{for all } t \ge 0,$$

with $\|\cdot\|$ the supremum norm (van den Driessche–Watmough 2002, Theorem 2). The statement concerns
only solutions defined on all of $[0, \infty)$, so by itself it is not local exponential stability.
