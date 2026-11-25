# Tent Net forward

Construction half of Theorem 5.1: the network computes the `k`-fold
tent iterate. The forward pass through `2 * k` layers uses `3 * k` ReLU
nodes, three per block counting the readout ReLU; at `k = L^2 + 2` this
is `3 * L^2 + 6` nodes and `2 * L^2 + 4` layers. No approximation or
learnability claim is made.
