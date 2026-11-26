# Cokernel Precomp Short Complex Iso Data

Let $C$ be an abelian category and let $X,Y,Z,X'$ be cochain complexes in $C$
indexed by $\mathbb Z$. Take maps $f:X\to Y$ and $g:Y\to Z$, an isomorphism
$e:X'\cong X$, and a map $f':X'\to Y$ satisfying $f'=f\circ e.\mathrm{hom}$.
Let $T$ be a short complex of cochain complexes and take an isomorphism
$E:\operatorname{cokernelCompShortComplex}(f,g)\cong T$.

Write $P$ for `cokernelCompShortComplexPrecompIsoOfEq f g e f' h`, where $h$
is the specified equality. The construction supplies an isomorphism

$$
I:\operatorname{cokernelCompShortComplex}(f',g)\cong T
$$

together with a proof of the equality $I=E\circ P$ of complete
short-complex isomorphisms. Its first two component isomorphisms are the
corresponding composites of those of $P$ and $E$. Its third component is
directly the third component of $E$, using the identity third component of
$P$.
