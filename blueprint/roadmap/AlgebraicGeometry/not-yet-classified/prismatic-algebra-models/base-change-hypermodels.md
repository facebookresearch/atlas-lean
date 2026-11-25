# Base Change Hypermodels

Compatible algebra hyperresolutions along a base change: let $p$ be a prime, $(A, I) \to (B, J)$
a map of bounded prisms and $g : Y \to X$ a map from a $p$-adic formal scheme over
$\operatorname{Spf}(B/J)$ to one over $\operatorname{Spf}(A/I)$, over the induced map of formal
spectra (`PrismaticBaseChangeMaps.Map`), with derived global sections functors on both relative
prismatic sites, and $O$, $V$ structure algebra sheaves for $X$ and $Y$ (`StructuralAlgebra`). Then
there are hyperresolutions $H$ of $O$ and $K$ of $V$ by sheaves of algebras (`Hypermodel`), together
with ring maps from the sections of $H$ over the image of each object to the sections of $K$,
compatible with scalars, restrictions, the cosimplicial structure and the augmentations
(`SiteAlgebraMap`).
