# Cost of a vector in an orthogonal labeling

Fix a vector $c$ (the handle) in a real inner product space. The cost of a vector $x$ is

$$
\mathrm{cost}_c(x) = \frac{\langle c, x\rangle^2}{\lVert c\rVert^2 \lVert x\rVert^2},
$$

the squared cosine of the angle between $c$ and $x$; it is $0$ when $x = 0$ or $c = 0$. Scaling $x$ by a nonzero scalar does not change its cost.

Knuth takes the first coordinate vector as handle, so that the cost of a unit vector is the square of its first coordinate; Lovász allows any unit handle. An orthogonal change of coordinates moves any unit handle to the first coordinate vector (Knuth, Lemma 0), so the two conventions give the same theta function.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §1 (definition of $c(a_v)$) and Lemma 0.
