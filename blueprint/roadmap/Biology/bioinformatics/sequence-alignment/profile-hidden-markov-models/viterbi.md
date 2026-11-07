# Viterbi value of a sequence under a profile HMM

The Viterbi value of a sequence `x`: the value selected by the max recursion
(`pathProb_le_viterbi`, `exists_pathProb_eq_viterbi`). Under nonnegative weights it is the
largest weight of a path through the model emitting `x`.
