# Norm bound from a quadratic-form bound

Let $A$ be a symmetric real matrix indexed by a finite set that maps vectors with zero sum to vectors with zero sum, and let $c \ge 0$ satisfy $\lvert x^{\mathsf T} A x\rvert \le c\, x^{\mathsf T} x$ for every $x$ with zero sum. Then $\lVert A x\rVert \le c \lVert x\rVert$ for every such $x$: the variational characterisations $\max \lvert\langle \alpha, M\alpha\rangle\rvert/\langle\alpha, \alpha\rangle$ and $\max \lVert M\alpha\rVert/\lVert\alpha\rVert$ over $\alpha \perp \mathbf 1$ agree (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 2.2). The proof polarizes: $4t \lVert Ax\rVert^2 \le c(\lVert Ax + tx\rVert^2 + \lVert Ax - tx\rVert^2)$, with $t = c$ (or $t = 1$ if $c = 0$).

## Background

- [$(N, D, \lambda)$-graph given by a rotation map](is-ndlambda-graph.md): the norm form that this lemma
  produces from the quadratic-form bound proved in the zig-zag analysis.
