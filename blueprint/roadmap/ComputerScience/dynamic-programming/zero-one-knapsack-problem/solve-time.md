# Exact cost of the knapsack algorithm

For every list of $n$ knapsack items and every
capacity $W \in \mathbb{N}$, the bottom-up knapsack algorithm costs exactly $n(W + 1) + n$ ticks:
one for each of the $n(W + 1)$ table cells it computes and one for each of the $n$ item rows it
inspects during reconstruction.
