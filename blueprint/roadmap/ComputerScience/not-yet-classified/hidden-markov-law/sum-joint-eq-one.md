# HMM joint law sums to one

Let $h$ be a hidden Markov model over finite state and observation sets whose initial weights form a probability distribution and whose transition and emission rows are probability distributions. For every $t \in \mathbb{N}$, the joint weight $\pi(z_0) e(z_0, x_0) \prod_{i=1}^{t} a(z_{i-1}, z_i)\, e(z_i, x_i)$, summed over all observation strings $x \in O^{t+1}$ and all state paths $z \in S^{t+1}$, equals $1$.
