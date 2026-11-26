# Tensor product of free sheaves is free on the product set

Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For arbitrary `A,B
: Type u`, `freeTensorIso R A B : free_{R_s} A ⊗ free_{R_s} B ≅ free_{R_s}(A×B)` has forward
map `FreeTensor.forwardHom` and inverse `FreeTensor.backwardHom`, where `R_s` is the
underlying ring sheaf.
