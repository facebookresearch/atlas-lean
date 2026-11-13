# Closed form of the Hedge weights

For every learning rate $\eta$, sequence of rounds,
initial weights $w$ and expert $i$, the weight of expert $i$ after running Hedge on the rounds from
$w$ is $w_i e^{-\eta L_i}$, where $L_i$ is expert $i$'s total loss over the rounds.
