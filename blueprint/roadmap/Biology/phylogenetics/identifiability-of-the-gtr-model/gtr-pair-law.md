# Gtr Pair Law

The **pair-site law** of a GTR branch of length `t`: `π i * P t i j`. For a branch length
`t ≥ 0` it is the joint probability that a site is in state `i` at one end of the branch (drawn
from the stationary base frequencies) and in state `j` at the other end, that is, the law of an
aligned site pattern for two taxa joined by a branch of length `t` (`gtrPairLaw_nonneg`,
`sum_sum_gtrPairLaw`). The formula is defined for every real `t`, but for `t < 0` its entries
can be negative, so it is not a probability law there.
