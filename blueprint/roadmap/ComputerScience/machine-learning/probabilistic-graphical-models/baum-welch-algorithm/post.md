# Posterior weight of a state path

For a valid HMM $h$, observation sequences
$x_0, \dots, x_{N-1}$, an index $n < N$ and a state path $z = (z_0, \dots, z_T)$, the posterior
weight of $z$ is the posterior of $z$ given $x_n$ at $h$ in the EM model of HMMs: the path weight
of $z$ and $x_n$ divided by the sum of the path weights of $z'$ and $x_n$ over all state paths
$z' = (z'_0, \dots, z'_T)$.
