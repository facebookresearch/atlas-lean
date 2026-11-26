# The represented coefficient gives a Tor object at the shared height

Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). rawLieCoefficientTorAt M n is (F_H.leftDerived n).obj T_H in
ModuleCat.{H} R. The coefficient and trivial input are their explicit lifts.
