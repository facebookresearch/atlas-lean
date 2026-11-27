# The cut direction has unit $A^{-1}$-norm

If $A$ is positive definite and $c \ne 0$, the [cut direction](cut-direction.md) $b = A c/\sqrt{c^\top A c}$ satisfies $b^\top A^{-1} b = 1$: indeed $A^{-1} b = c / \sqrt{c^\top A c}$, so $b^\top A^{-1} b = (A c)^\top c / (c^\top A c) = 1$. Thus $a \pm b$ lies on the boundary of $E(a, A)$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, equations (3)-(5).
