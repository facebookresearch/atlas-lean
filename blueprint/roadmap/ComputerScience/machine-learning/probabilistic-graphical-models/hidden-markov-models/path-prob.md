# Joint weight of a state path and the observations

For a hidden Markov model $h$ with
initial weights $\pi$, transition weights $a$ and emission weights $b$ in a semiring, observations
$x_0, x_1, \dots$ and $t \in \mathbb{N}$, the joint weight of a state path $z = (z_0, \dots, z_t)$
and $x_0, \dots, x_t$ is the product, taken from left to right,
$\pi(z_0)\, b(z_0, x_0)\, a(z_0, z_1)\, b(z_1, x_1) \cdots a(z_{t-1}, z_t)\, b(z_t, x_t)$.
