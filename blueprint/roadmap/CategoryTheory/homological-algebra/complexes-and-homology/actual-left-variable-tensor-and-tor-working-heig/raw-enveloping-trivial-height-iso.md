# The trivial module's repeated input lift has its canonical flattening

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. rawEnvelopingTrivialHeightIso identifies I_U(T_H)
with T_H', the trivial enveloping module at the larger height, by
ModuleCat.uliftFunctorCompIso.
