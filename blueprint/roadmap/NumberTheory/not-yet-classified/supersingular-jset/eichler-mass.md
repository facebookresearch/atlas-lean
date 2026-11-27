# Eichler Mass

The Eichler mass of level `N` in prime characteristic `p`, defined as `(p - 1) * ψ(N) / 12`,
where `ψ` is the Dedekind psi function `ArithmeticFunction.dedekindPsi`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`).

Eichler's mass formula with the Deuring correspondence (J. Voight, *Quaternion Algebras*,
Theorem 25.3.18 and Remark 42.3.10) states that, for a level `N ≥ 1` not divisible by `p`, it
equals the sum of `2 / |Aut(E, C)|` over the supersingular points `(E, C)` of `X₀(N)` over an
algebraic closure of `ZMod p`. Here `C` is a cyclic subgroup of `E` of order `N`, and `Aut(E, C)`
is the group of the automorphisms of `E` that map `C` onto itself, not the group `Aut(E)` of all
automorphisms of `E` that `autWeight` uses; the two agree at level `1`.
