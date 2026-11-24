# Node Complex Power

Complex power supplied by a node to the branch and shunt network:
voltage times conjugated injection, in the canonical root-mean-square
convention. The injection is the current leaving the node into the
network, so this is the power the network absorbs through that node.
It is a per-phase quantity: in balanced three-phase operation the three
phases supply `3` times this value (`sum_nodeComplexPower_balancedPhases`).
New definition owned by this module.
