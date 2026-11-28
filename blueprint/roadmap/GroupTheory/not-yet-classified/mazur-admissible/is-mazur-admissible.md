# Mazur-admissible Galois module

`M` is Mazur admissible at `p` for `Φ` if `p` is prime and
`M` admits an admissible chain for `p`: the Galois module `M` has an admissible filtration in
Mazur's sense, a filtration by Galois submodules whose successive quotients are isomorphic to the
Galois modules `ℤ/p` (trivial action) or `μ_p` (action through the mod-`p` cyclotomic character).
Primality is part of the definition because a chain only asks each quotient to have `Nat.card` equal
to `p`, and `Nat.card` of an infinite type is `0`, so at `p = 0` the group `ℤ` with the trivial
action has a chain. It is a condition on the Galois module only, not Mazur's notion of an admissible
group scheme.
