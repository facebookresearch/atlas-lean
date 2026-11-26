# The balanced tensor height equivalences are natural in the left input

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. The objectwise coordinates give
rawTensorHeightNatIso : I_U ⋙ F_H' ≅ F_H ⋙ V_R.
