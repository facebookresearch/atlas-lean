# Profile hidden Markov models

## The model

- [State types of a profile HMM node](profile-state.md)
- [Profile hidden Markov model](profile-hmm.md)
- [Consensus columns of a profile HMM](columns.md)
- [HMMER Plan 7 restrictions](is-plan7.md)

## Path weights and the forward value

- [Profile HMM as an alignment automaton](to-automaton.md)
- [Weight of a path through a profile HMM](path-prob.md)
- [Forward value of a sequence under a profile HMM](forward.md)
- [Forward computes the total path weight](forward-eq-sum.md)

## The Viterbi value

- [Viterbi value of a sequence under a profile HMM](viterbi.md)
- [Nonnegative weights of a profile HMM](nonneg.md)
- [Nonnegative profile HMM gives a nonnegative alignment automaton](to-automaton-nonneg.md)
- [Every path weighs at most the Viterbi value](path-prob-le-viterbi.md)
- [The Viterbi value is attained](exists-path-prob-eq-viterbi.md)

## Emission estimates with pseudocounts

- [Pseudocount emission estimate of a match state](pseudocount-emission.md)
- [Pseudocount emission estimates sum to one](sum-pseudocount-emission.md)
- [Pseudocount emission estimates are positive](pseudocount-emission-pos.md)
