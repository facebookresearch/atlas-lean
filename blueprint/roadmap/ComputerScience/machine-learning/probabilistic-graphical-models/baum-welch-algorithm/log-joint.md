# The log path weight is linear in the path's counts

Let $S$ and $O$ be finite sets, let
$T$ be a natural number, and let $h$ be a valid hidden Markov model on states $S$ and observations
$O$, with positive initial probabilities $\pi_s$, transition probabilities $a_{ss'}$ and emission
probabilities $b_{so}$, each distribution summing to one. For every observation sequence
$x = (x_0, x_1, \dots)$ in $O$ and every state path $z = (z_0, \dots, z_T)$ in $S$, the path
weight $p_h(x, z) = \pi_{z_0} b_{z_0 x_0} \prod_{t=1}^{T} a_{z_{t-1} z_t} b_{z_t x_t}$ satisfies
$\log p_h(x, z) = \sum_{s} [z_0 = s] \log \pi_s + \sum_{s, s'} n_{ss'} \log a_{ss'} +
\sum_{s, o} m_{so} \log b_{so}$, where $[z_0 = s]$ is $1$ if $z_0 = s$ and $0$ otherwise,
$n_{ss'} = \#\{t < T : z_t = s,\ z_{t+1} = s'\}$ and $m_{so} = \#\{t \le T : z_t = s,\ x_t = o\}$.
