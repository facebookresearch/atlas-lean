# Natural split evaluation is a block-label sum

Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For `m : ℕ`, `splitEulerianLambda p q m` equals the sum over `g : Fin p → Fin m` and `h : Fin
q → Fin m`, with contribution `sign(blockPermutation(sort g,sort h)) [blockPermutation(sort
g,sort h)]`.
