# Polar decomposition

Every complex square matrix $A$ factors as $A = UP$ with $U$ unitary and $P$ positive semidefinite, $P^2 = A^* A$, where $A^*$ is the conjugate transpose.

## Idea

The polar decomposition is the matrix analogue of writing a complex number as $z = e^{i\theta} |z|$: the factor $P = (A^*A)^{1/2}$ plays the role of the modulus and $U$ the role of the phase. It follows from the singular value decomposition $A = W\Sigma V^*$ by taking $U = WV^*$ and $P = V\Sigma V^*$. For an invertible matrix the factors are unique and $P$ is positive definite; over the reals, $U$ is orthogonal and $P$ symmetric. For a real rectangular matrix $G$, a compact SVD $G = U_r \Sigma_r V_r^{\mathsf T}$ gives the canonical polar factor $U_r V_r^{\mathsf T}$ (with $V_r^*$ in place of $V_r^{\mathsf T}$ for a complex matrix), a partial isometry, zero for the zero matrix. For an invertible real square $G$ it is the orthogonal factor of the polar decomposition; for a singular square $G$ it is not orthogonal, though it extends to an orthogonal polar factor.

## Statements

- [Polar decomposition of a complex square matrix](exists-unitary-group-pos-semidef.md)
- [Uniqueness of the polar decomposition of an invertible matrix](exists-unique-unitary-group-pos-def-of-i.md): uniqueness for invertible matrices
- [Polar decomposition of invertible complex matrices](polar-decomposition-gl-complex.md): invertible complex matrices
- [Polar decomposition of invertible real matrices](polar-decomposition-gl-real.md): invertible real matrices: orthogonal times positive definite symmetric
- [Canonical polar factor of a rectangular matrix](rectangular-polar-factor.md): defined from a compact singular value decomposition
- [Properties of the canonical polar factor](canonical-polar-factor-properties.md): the orthogonal factor for an invertible real square matrix; otherwise a canonical partial isometry
