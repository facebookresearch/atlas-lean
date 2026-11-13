# Passage to the limit in the speed

Let `(Uₙ, Uₙ')` solve the profile equation at speed
`cₙ ∈ (0, c₁]` on `[a, b]` and stay in the trapping triangle there. If `cₙ → c` and
`(Uₙ, Uₙ') → (U, V)` pointwise on `[a, b]`, then `(U, V)` solves the profile equation at the
limit speed `c` on `(a, b)`. With `cₙ ↓ 2 √(r D)` this is the route to the critical-speed
front: the equi-Lipschitz bounds `abs_sub_le_of_mapsTo_trappingTriangle` supply the convergent
subsequence (Arzelà–Ascoli, not formalized here), `closedTriangle_of_tendsto` keeps the limit in
the closed critical triangle, and this theorem identifies the limit as a solution.

Proof: no integrals. Uniform Lipschitz bounds on `Uₙ'` and on `Uₙ''` give quadratic Taylor
remainders with constants independent of `n`; these survive the pointwise limit and force the
derivatives of the limit.
