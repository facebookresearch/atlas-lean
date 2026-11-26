# Tor at two shared heights agrees through output lifting and input flattening

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For n : ℕ, rawLieCoefficientTorHeightIsoAt
identifies V_R(Tor_H(M,n)) with Tor_H'(M,n), using the derived height functor isomorphism at
T_H followed by the map of the trivial-input flattening.
