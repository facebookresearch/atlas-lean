# Tensor unit as the structure module sheaf

Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. The isomorphism `tensorUnitIso R : 𝟙_ ≅ SheafOfModules.unit R_ring`
identifies the monoidal tensor unit with the structure sheaf regarded as a module, where
`R_ring=(sheafCompose J (forget₂ ..)).obj R`.
