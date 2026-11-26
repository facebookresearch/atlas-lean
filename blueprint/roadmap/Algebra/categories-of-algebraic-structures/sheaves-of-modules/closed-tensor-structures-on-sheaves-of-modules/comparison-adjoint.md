# Adjoint form of the sheafification-restriction comparison

Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
the locally-bijective comparison, and underlying-ring sheaf comparisons on the base and a
slice over `X`. Write `q_X=restrictPresheaf`, `F_X=restrictSheaf`, `L_R=sheafificationBase`,
and `U_X=forgetRestrictOver`. For a module presheaf `A`, `comparisonAdjoint R X A : q_X A →
U_X(F_X(L_R A))` is `q_X(η_A)` followed by `forgetRestrictIso` at `L_R A`, where `η` is the
base sheafification unit.
