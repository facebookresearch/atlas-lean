# Determinant Extension

The condition that the determinant map of a base-changed two-term complex is a scalar extension.
Let $P$ be a two-term complex of finite projective $R$-modules, $g : R \to S$ a ring homomorphism,
`C` the conditions `ScalarComplexData` on the termwise extension of scalars $S \otimes_R P$, `U` the
fact that each unit map $P^i \to S \otimes_R P^i$ is a scalar extension, and `T` determinant
base-change maps for the terms in degrees $-1$ and $0$. The condition is that the $g$-semilinear map
`determinantMap` from $\operatorname{Hom}_R(\det P^{-1}, \det P^0)$ to
$\operatorname{Hom}_S(\det(S \otimes_R P^{-1}), \det(S \otimes_R P^0))$ induced by `T` is a scalar
extension (`IsScalarExtension`): composition with it is a bijection from $S$-linear maps out of its
target to $g$-semilinear maps out of its source, into every $S$-module. Here $\det$ is the
determinant module `determinantModule`.
