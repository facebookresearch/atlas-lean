# Invertible row operations preserve the null space

Let $K$ be a field, let $m$ and $n$ be
finite linearly ordered sets, let $A$ be an $m \times n$ matrix over $K$, and let $P$ be an
invertible $m \times m$ matrix over $K$. Then the linear maps $x \mapsto PAx$ and $x \mapsto Ax$
on $K^n$ have the same kernel; that is, the homogeneous systems $PAx = 0$ and $Ax = 0$ have the
same solutions.

Proof: For every $x \in K^n$ we have $(PA)x = P(Ax)$, and multiplication by $P$ is injective
because $P$ is invertible, so $(PA)x = 0$ if and only if $Ax = 0$.

## Sources

- Mathlib `docs/undergrad.yaml`, Linear algebra / Matrices / elementary row operations; G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
