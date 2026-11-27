# Is Jump Hold

`(Y, E)` under `P` is a jump–hold realization of the chain with rates `q`: `P` is a
probability measure; each `Y n` is measurable; the probability that `Y` starts with a given path
is that of its first state times the factors `ENNReal.ofReal (jumpProb q y y')` of its steps, so
that `Y` is a Markov chain with transition probabilities `jumpProb q` (and arbitrary initial law)
when every off-diagonal row of `q` is nonnegative and summable; the clocks `E n` are independent
and exponential of rate `1`; and the clocks are independent of `Y`.
