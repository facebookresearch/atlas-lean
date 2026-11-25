# Aut Weight

The automorphism weight of a supersingular `j`-invariant in prime characteristic `p`: half the
order of the automorphism group of an elliptic curve `E` over an algebraic closure of `ZMod p`
with `j`-invariant `j`, that is, the order of `Aut E / {±1}`. It is `12` in characteristic `2` at
`j = 0` (`|Aut E| = 24`), `6` in characteristic `3` at `j = 0` (`|Aut E| = 12`), `3` at `j = 0`
(`|Aut E| = 6`) and `2` at `j = 1728` (`|Aut E| = 4`) in characteristic greater than `3`, and `1`
otherwise (`|Aut E| = 2`); see J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
Theorem III.10.1. So `1 / autWeight p j` is the normalized weight `2 / |Aut E|`, and in this
normalization the Eichler mass formula (J. Voight, *Quaternion Algebras*, (42.3.9)) reads
`∑ 1 / autWeight p j = eichlerMass 1 p`, the sum running over the supersingular `j`. This file
computes neither the automorphism groups nor the mass formula. Defined for prime fields `ZMod p`
only: prime-power fields `𝔽_q` with `q = p ^ n`, `n > 1`, are out of scope.
