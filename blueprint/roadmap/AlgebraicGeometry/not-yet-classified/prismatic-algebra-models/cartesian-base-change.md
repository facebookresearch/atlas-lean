# Cartesian Base Change

Base change for prismatic cohomology (Bhatt–Scholze, Corollary 4.12): let $p$ be a prime,
$(A, I) \to (B, J)$ a map of bounded prisms and $g : Y \to X$ a map from a $p$-adic formal scheme
over $\operatorname{Spf}(B/J)$ to one over $\operatorname{Spf}(A/I)$, over the induced map of formal
spectra (`PrismaticBaseChangeMaps.Map`), such that derived scalar extension along $A \to B$ exists
(`HasExtension`), $g$ is Cartesian at every level, $X$ is smooth, quasi-compact and quasi-separated
at every level, and both relative prismatic sites have derived global sections functors. Fix
structure algebra sheaves with compatible hyperresolutions $H$, $K$ and a map between them
(`SiteAlgebraMap`), algebra structures on their global cochains with an algebra map realizing it
(`AlgebraMap`), and a derived $(p, J)$-completion functor on $B$-modules, and assume the global
cochains of $K$ derived $(p, J)$-complete. Then the induced map from the completed base change
$R\Gamma_\Delta(X/A) \hat{\otimes}^L_A B$ to $R\Gamma_\Delta(Y/B)$ is an isomorphism. The
quasi-compactness and quasi-separatedness hypotheses are needed: for a countable disjoint union of
copies of the base, the completed tensor product does not commute with the infinite product of
global sections.
