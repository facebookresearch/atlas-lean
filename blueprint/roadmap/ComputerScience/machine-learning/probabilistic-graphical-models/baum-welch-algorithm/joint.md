# The EM model of a hidden Markov model

Let $S$ and $O$ be finite sets and let $T$ be a
natural number. Let $h$ be a valid hidden Markov model on states $S$ and observations $O$, with
positive initial probabilities $\pi_s$, transition probabilities $a_{ss'}$ and emission
probabilities $b_{so}$, each distribution summing to one. The joint of its EM model at an
observation sequence $x = (x_0, x_1, \dots)$ in $O$ and a state path $z = (z_0, \dots, z_T)$ in $S$
is the path weight $p_h(x, z) = \pi_{z_0} b_{z_0 x_0} \prod_{t=1}^{T} a_{z_{t-1} z_t} b_{z_t x_t}$.
