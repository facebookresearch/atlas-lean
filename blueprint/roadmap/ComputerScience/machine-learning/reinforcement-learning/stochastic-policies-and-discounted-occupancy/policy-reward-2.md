# Expected reward under a row-stochastic policy

For a Markov decision process with finite sets of states and actions and rewards $r(s, a)$, and a
real matrix $\pi(s, a)$, let $r^\pi(s) = \sum_a \pi(s, a)\, r(s, a)$. When $\pi$ is row-stochastic
(nonnegative entries, each row summing to $1$), $r^\pi(s)$ is the expected one-step reward in state
$s$ under the policy $\pi$. This is the [expected reward of a stochastic policy](policy-reward.md)
with the policy given as a matrix.
