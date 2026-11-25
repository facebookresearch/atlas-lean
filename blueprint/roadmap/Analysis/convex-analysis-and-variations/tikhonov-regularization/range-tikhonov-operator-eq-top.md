# Tikhonov normal operator is surjective

Let $H$ and $K$ be Hilbert spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $A : H \to K$ a
bounded linear operator and $\Lambda > 0$. Then the [normal operator](tikhonov-operator.md)
$A^* A + \Lambda I$ is surjective: its range is closed (the operator is bounded below by $\Lambda$),
the orthogonal complement of its range is its kernel because the operator is self-adjoint, and the
kernel is trivial because $\operatorname{Re}\langle (A^* A + \Lambda I) x, x\rangle = \|Ax\|^2 + \Lambda \|x\|^2 > 0$
for $x \ne 0$.
