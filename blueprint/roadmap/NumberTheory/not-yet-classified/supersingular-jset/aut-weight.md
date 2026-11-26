# Aut Weight

The automorphism weight of `j : ZMod p` in prime characteristic `p`, defined by cases: `12` in
characteristic `2` at `j = 0`, `6` in characteristic `3` at `j = 0`, `3` at `j = 0` and `2` at
`j = 1728` in characteristic greater than `3`, and `1` otherwise. The hypothesis `[Fact p.Prime]`
makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for `n > 1`).

These values are half the order of `Aut(E)`, the group of all automorphisms of an elliptic curve
`E` over an algebraic closure of `ZMod p` with `j`-invariant `j`, that is, the order of
`Aut(E) / {±1}`: `|Aut(E)|` is `24`, `12`, `6`, `4` and `2` in the five cases (J. H. Silverman,
*The Arithmetic of Elliptic Curves*, 2nd ed., Theorem III.10.1). So for `j` in `ZMod p` the
weight `2 / |Aut(E)|` is `1 / autWeight p j`. A supersingular `j` outside `ZMod p` is neither `0`
nor `1728`, so its weight `2 / |Aut(E)|` is `1`. The level-one mass formula
`∑ 1 / |Aut(E)| = (p - 1) / 24` (J. Voight, *Quaternion Algebras*, (42.3.9)) reads
`∑ 2 / |Aut(E)| = eichlerMass 1 p`, the sum running over the supersingular `j` in an algebraic
closure of `ZMod p`. For `p ≤ 13` all of them lie in `ZMod p`, so the sum is that of
`1 / autWeight p j` over them. At a level `N > 1` not divisible by `p`, the weights of
`eichlerMass N p` use the automorphisms `Aut(E, C)` of `E` that preserve a cyclic subgroup `C` of
order `N` instead.
