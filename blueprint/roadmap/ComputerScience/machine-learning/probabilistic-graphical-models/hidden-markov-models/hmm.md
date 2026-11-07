# Hidden Markov model

A hidden Markov model with a set of states $S$, a set of observations
$O$ and weights in $R$ consists of an initial weight $\pi(s) \in R$ for each state $s$, a
transition weight $a(s, s') \in R$ for each pair of states, the weight of a transition from $s$
to $s'$, and an emission weight $e(s, o) \in R$ for each state $s$ and observation $o$, the
weight of emitting $o$ from $s$.

No structure on $R$ and no normalization of the weights is required.
