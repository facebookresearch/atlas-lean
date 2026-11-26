# The inverse Tor height map inserts the trivial lift then applies the derived square

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. The inverse is (F_H'.leftDerived
n).map(rawEnvelopingTrivialHeightIso.inv) followed by the component at T_H of
leftDerivedSquareHom(I_U,V_R,rawTensorHeightNatIso.hom).
