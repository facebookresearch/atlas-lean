# Ss Count Formula

The supersingular count formula of level `N` in prime characteristic `p`, defined as
`eichlerMass N p + (2 - ν₂(p)) * ν₂(N) / 4 + (2 - ν₃(p)) * ν₃(N) / 3`, where `ν₂ = nuTwo` and
`ν₃ = nuThree` count the roots of `x ^ 2 + 1` and of `x ^ 2 + x + 1` in `ZMod N` and in the field
`ZMod p`. The hypothesis `[Fact p.Prime]` makes `ZMod p` the field with `p` elements
(`ZMod (p ^ n)` is not a field for `n > 1`).

For a level `N ≥ 1` not divisible by `p`, Eichler's class number formula (J. Voight, *Quaternion
Algebras*, Theorem 30.1.5) gives this value as the class number of an Eichler order of level `N`
in the quaternion algebra over `ℚ` ramified at `p` and `∞`, which by the Deuring correspondence
(Remark 42.3.10 there) is the number of supersingular points `(E, C)` of `X₀(N)` over an algebraic
closure of `ZMod p`, counted without weights.
