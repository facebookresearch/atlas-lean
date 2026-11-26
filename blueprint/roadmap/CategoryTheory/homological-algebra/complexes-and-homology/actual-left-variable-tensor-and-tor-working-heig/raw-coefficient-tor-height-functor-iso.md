# The balanced tensor height square gives an isomorphism of derived functors

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For n : ℕ, rawCoefficientTorHeightFunctorIso is
(F_H.leftDerived n) ⋙ V_R ≅ I_U ⋙ (F_H'.leftDerived n). It uses projective preservation for
I_U and homology preservation for V_R.
