# Tuple evaluation formula for a graded pairing

For a graded pairing P:K₁⊗K₂ → K₃ of nonnegative cochain complexes of
abelian groups, choose tuple types T_p,U_q,V_n, value types X,Y,Z,
evaluations left_p:K₁ᵖ → T_p → X, right_q:K₂ᑫ → U_q → Y,
target_n:K₃ⁿ → V_n → Z, maps front_{p,q}:V_{p+q} → T_p and
back_{p,q}:V_{p+q} → U_q, and pair:X → Y → Z.
The tuple pairing property is the equality, for all p,q,a,b,v,
target_{p+q}(P_{p,q}(a⊗₍ℤ₎b))(v)
=pair(left_p(a)(front_{p,q}(v)),right_q(b)(back_{p,q}(v))).
