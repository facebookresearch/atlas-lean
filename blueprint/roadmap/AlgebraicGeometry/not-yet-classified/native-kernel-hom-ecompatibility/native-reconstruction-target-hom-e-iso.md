# Native reconstruction target Hom E iso

For a given $M$, an isomorphism between the ringed reconstruction target and the enhanced Hom
target of a kernel $\mathcal{K}$. Let $X$ be a Hausdorff complex manifold of dimension $n$ with the
given interface data, $M$ an object of the derived category of modules over the ring of analytic
differential operators on $X$, and $\mathcal{K}$ (`Kernel`) an object of the enhanced
$\mathcal{D}$-module quotient such that the solution complex of $M$ with kernel $\mathcal{K}$ is
bounded (`BoundedSolution`); let $S$ be its class in the enhanced category. Assume that the
coefficient functor descends to the enhanced quotient (`Factor`, the statement of
`native_module_coefficients_descend`), that the enhanced quotient of coefficients has a left
adjoint, that tensoring with each bounded coefficient complex has a right adjoint, and that the
pulled-back $\beta$-functor has a right adjoint. This constructs an isomorphism, in the derived
category of sheaves of complex vector spaces on $X$, from `reconstructionCoefficientsTarget`, the
underlying complex of the ringed reconstruction target of $M$ (the right adjoint of the pulled-back
$\beta$-functor applied to the internal Hom from the left representative of $S$ to the right
representative of $\mathcal{K}$), to `scalarHomETarget`, the enhanced Hom
$\alpha\,R\pi_*\,R\mathcal{I}hom(L^E S, R^E K)$ from $S$ to the coefficient image $K$ of
$\mathcal{K}$. The isomorphism is not required to be natural in $M$ or compatible with the
reconstruction morphism `originalReconstructionMap` (D'Agnolo–Kashiwara, Proposition 9.5.1).
