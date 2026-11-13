# Loss of a Hedge round

For weights $w$ and losses $\ell$ on $n$ experts, the algorithm's
loss in the round is $\left(\sum_i w_i \ell_i\right) / W$, where $W = \sum_i w_i$ is the total
weight. This is its expected loss when it follows expert $i$ with probability $w_i / W$.
