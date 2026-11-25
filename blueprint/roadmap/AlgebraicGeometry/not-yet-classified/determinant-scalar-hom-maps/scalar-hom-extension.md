# Scalar Hom Extension

The proposition that extension of scalars commutes with Hom out of a finite projective module:
for a ring map $g : R \to S$, a finite projective $R$-module $M$, an $R$-module $N$, and
$g$-semilinear maps $a : M \to M'$ and $b : N \to N'$ exhibiting the $S$-modules $M'$ and $N'$ as
the scalar extensions of $M$ and $N$ (`IsScalarExtension`), the $g$-semilinear map
$\operatorname{Hom}_R(M, N) \to \operatorname{Hom}_S(M', N')$ sending $f$ to the unique $S$-linear
map $f'$ with $f' \circ a = b \circ f$ (`scalarHomMap`) exhibits $\operatorname{Hom}_S(M', N')$ as
the scalar extension of $\operatorname{Hom}_R(M, N)$.
