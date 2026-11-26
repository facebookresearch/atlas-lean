# Finite index count for tensor generators

Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For generating
families `G,H` and equivalences `eG : G.I ≃ Fin m`, `eH : H.I ≃ Fin n`, `tensorRankEquiv R G H
eG eH` gives `(GeneratingSections.tensor G H).I ≃ Fin (m*n)`. It counts the tensor generating
indices by the product of the two finite counts.
