# Composition with supplied terms

The compliance `J(Fhat, khat)` at the estimated inputs,
the compliance `Jmodel` of the analysis model, its discretization `Jdisc`, the algebraic solver
output `Jsolve` and the computed value `Jcomp` are successive values of the same compliance;
with the supplied bounds `eModel`, `eDisc`, `eSolve`, `eArith` on their successive differences,
`|J(F, k) - Jcomp|` is at most the parameter bound plus the four supplied terms.
