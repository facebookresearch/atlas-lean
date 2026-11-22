# HMM of ChromHMM parameters

The hidden Markov model of [ChromHMM parameters](params.md) has initial weights $\pi$, transition weights $a$ and emission weights $e(s, o) = B_{p_s}(o) = \prod_j p_{s,j}^{o_j}(1 - p_{s,j})^{1 - o_j}$ on the observations $o \in \{0, 1\}^d$.
