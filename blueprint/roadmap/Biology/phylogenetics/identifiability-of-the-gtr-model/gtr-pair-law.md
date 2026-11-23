# Pair-site law of a GTR branch

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. For real base frequencies `π`, exchangeabilities `s` and a
branch length `t`, the pair-site law of the branch is `F(π, s, t) i j = π i · exp (t · Q(π, s)) i j`
for states `i` and `j`. When `(π, s)` lies in the [GTR parameter domain](is-gtrparam.md) and
`t ≥ 0`, it is the joint probability that a site is in state `i` at one end of the branch, drawn
from the base frequencies, and in state `j` at the other end: the law of an aligned site pattern of
two taxa joined by a branch of length `t`. The formula is defined for every real `t`, but for
`t < 0` its entries can be negative, so it is not a probability law there.
