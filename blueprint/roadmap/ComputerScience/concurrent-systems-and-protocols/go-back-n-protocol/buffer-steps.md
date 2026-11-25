# Transitions of the two-place buffer

The transitions of the go-back-N two-place buffer
at occupancy $n \in \mathbb{N}$: if $n < 2$ it inputs on $\mathsf{acc}$ and moves to occupancy
$n + 1$, and if $n > 0$ it outputs on $\mathsf{del}$ and moves to occupancy $n - 1$. It has no
other transitions.
