# Loss of a Hedge round

For weights $w$ and losses $\ell$ on $n$ experts, the algorithm's
loss in the round is $\left(\sum_i w_i \ell_i\right) / W$, where $W = \sum_i w_i$ is the total
weight (the quotient is $0$ when $W = 0$); the weights are arbitrary real numbers. For nonnegative weights with
$W > 0$, this is its expected loss when it follows expert $i$ with probability $w_i / W$.
