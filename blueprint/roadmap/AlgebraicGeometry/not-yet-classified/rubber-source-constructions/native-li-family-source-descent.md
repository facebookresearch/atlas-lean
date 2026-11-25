# Native Li Family Source Descent

The global source complex of Li's family deformation theory for rubber maps: let $k$ be an
algebraically closed field of characteristic zero, with the rubber target data `O`, `P`, `D`, `R`,
`S` over $k$, a genus $g$, a ramification profile $a \in \mathbb{Z}^n$ with $\sum_i a_i = 0$ and
$2g + n > 2$, and a rubber moduli model `B`. Then there is a descent datum
(`LiFamilySourceDescent.Descent`): a global cochain complex on the affine points of the moduli
stack, cofibrant at every point, with an étale surjective map from a chart point onto every
Noetherian affine point of finite type over $k$ (`SourceCover`), quasi-isomorphic base-change maps
along every map of affine points, quasi-isomorphisms from its evaluation at every chart point to
the local quotient complex, and homotopies relating these augmentations along every arrow after
refinement.
