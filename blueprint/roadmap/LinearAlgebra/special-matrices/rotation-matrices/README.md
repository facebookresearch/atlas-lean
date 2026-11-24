# Real planar rotation matrices

For $\theta \in \mathbb{R}$, the rotation matrix through the angle $\theta$ is

$$R(\theta) = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}.$$

It satisfies $R(a)R(b) = R(a + b)$ and $R(\theta)^{\mathsf T} = R(-\theta) = R(\theta)^{-1}$, so it is orthogonal with determinant $1$.

## Idea

The rotation matrices are the matrices of the special orthogonal group $\mathrm{SO}(2)$, and $\theta \mapsto R(\theta)$ is a homomorphism from the additive group of angles onto it. Identifying $\mathbb{R}^2$ with $\mathbb{C}$, the rotation $R(\theta)$ is multiplication by $e^{i\theta}$, so the addition formula $R(a)R(b) = R(a + b)$ is the addition formula for sine and cosine. Block-diagonal matrices of rotations act on $\mathbb{R}^{2k}$ and satisfy $R_\Theta(m)^{\mathsf T} R_\Theta(n) = R_\Theta(n - m)$; this relative-position property is what rotary position embeddings in transformer models rely on.

## Statements

- [Real planar rotation matrices](real-planar-rotation-matrices.md)
- [Identities of planar rotation matrices](rotation-matrix-identities.md): composition, transpose and inverse, determinant and norm, and the complex form
- [Block-diagonal rotation matrices](block-diagonal-rotations.md): orthogonality and the relative-position identity
