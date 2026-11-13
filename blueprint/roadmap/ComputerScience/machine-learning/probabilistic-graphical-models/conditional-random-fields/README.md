# Conditional random fields

- [Linear-chain conditional random field](chain-crf.md)
- [Weight of a label path in a chain CRF](path-weight.md)
- [Partition function of a chain CRF](partition.md)
- [Forward variables of a chain CRF](forward.md)
- [The forward variables are path weights](forward-eq.md)
- [The forward algorithm computes the partition function](partition-eq-sum-forward.md)

## Viterbi

- [The Viterbi variables of a chain CRF](viterbi.md)
- [Path weights of a chain CRF are bounded by the Viterbi variables](path-weight-le-viterbi.md)
- [The Viterbi variables of a chain CRF are attained](exists-path-weight-eq-viterbi.md)
- [Viterbi computes the MAP value of a chain CRF](sup-viterbi-eq.md)

## Conditional probabilities

- [Conditional probability of a label path in a chain CRF](cond-prob.md)
- [The conditional probabilities sum to $1$](sum-cond-prob-eq-one.md)
- [Conditional probabilities of a chain CRF are nonnegative](cond-prob-nonneg.md)

## Every HMM embeds as a CRF

- [The chain CRF of a hidden Markov model](hmm-to-crf.md)
- [The chain CRF of a hidden Markov model has the same path weights](hmm-to-crf-path-weight.md)

## Tabulated algorithms on `Fin n`

- [One step of the tabulated CRF forward algorithm](forward-step.md)
- [Tabulated CRF forward algorithm](forward-tab.md)
- [The tabulated forward algorithm for chain CRFs](partition-tab.md)
- [One step of the tabulated Viterbi recursion for a chain CRF](viterbi-step.md)
- [The tabulated Viterbi variables of a chain CRF](viterbi-tab.md)
- [Backpointer of the tabulated CRF Viterbi algorithm](back.md)
- [Backtracked path of the tabulated CRF Viterbi algorithm](best-path.md)
- [The backtracked path of a chain CRF attains the Viterbi variable](path-weight-best-path.md)
- [The Viterbi path of a chain CRF](crf-path.md)
- [The Viterbi path of a chain CRF has maximal weight](path-weight-le-crf-path.md)
