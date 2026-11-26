# Balanced tensor height coordinates apply factor down and output up

Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For X : ModuleCat.{H} U, rawTensorHeightEquiv
identifies F_H'(I_U X) with V_R(F_H X). It sends a balanced class [m',x'] to
ULift.up[θ(m'),x'.down], where θ : N_H' ≃ₗ[Uᵐᵒᵖ] N_H is the coefficient height equivalence.
