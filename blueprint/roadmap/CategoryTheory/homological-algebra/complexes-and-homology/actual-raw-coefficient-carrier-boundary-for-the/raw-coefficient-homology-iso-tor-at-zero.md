# The lifted degree-zero comparison retains the coefficient-unit tensor square

Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. Let Φ_H be the categorical CE/Tor comparison, d₀
= F_H.fromLeftDerivedZero at T_H, c_T the trivial-input lift cancellation and t_H the
coefficient homology transport. Then Φ_H,0.hom ≫ d₀ ≫ c_T equals t_H,0.hom followed by
nativeCoefficientHomologyZeroTensorIso for M_H.
