# Pair hidden Markov model

A pair HMM over the alphabet `α` with weights in `R` (Durbin et al., chapter 4): the
transition weights from the silent begin state (`start`) and between emitting states (`trans`),
to the silent end state (`stop` from an emitting state, `startStop` for the empty alignment),
and the emission weights of the three emitting states.
