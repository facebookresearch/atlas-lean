# Contraction of the minimizing-movement step

Let $H$ be a real inner product space, $F$ $\lambda$-convex and $h > 0$. If $y_1$ and $y_2$ are
[minimizing-movement steps](../minimizing-movements/is-minimizing-movement-step.md) from $x_1$ and $x_2$, then

$$(1 + \lambda h) \, \|y_1 - y_2\| \le \|x_1 - x_2\| .$$

When $1 + \lambda h > 0$ the step is $(1 + \lambda h)^{-1}$-Lipschitz, hence unique. Proof: add the
[variational inequalities](inner-le.md) of the two steps, tested against each other, and apply
the Cauchy–Schwarz inequality.

In Otto's picture, gradient flows of convex functionals contract, and contraction estimates for
dissipative equations are consequences of the convexity of the driving functional in the right
geometry; for the porous medium equation that convexity is McCann's displacement convexity in the
Wasserstein space. This theorem is the time-discrete, Hilbert-space instance of that principle.

## Background

- [Displacement convexity](../../displacement-convexity/README.md): the Wasserstein analogue of
  $\lambda$-convexity.

## Sources

- F. Otto, M. Westdickenberg, *Eulerian calculus for the contraction in the Wasserstein distance*, Section 1 (version read: http://www.instmath.rwth-aachen.de/~mwest/files/OttoWest.pdf).
