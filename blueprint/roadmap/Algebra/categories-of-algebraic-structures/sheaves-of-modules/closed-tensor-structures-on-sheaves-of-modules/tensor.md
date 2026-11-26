# Product-indexed generators for a tensor product of module sheaves

Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For arbitrary
generating families `G` of `M` and `H` of `N`, `GeneratingSections.tensor G H` generates `M ⊗
N` with index set `G.I × H.I`. Its presentation map is `(freeTensorIso R G.I H.I).inv ≫ (G.π ⊗
H.π)`.
