# Weight of a label path in a chain CRF

For a chain conditional random field with weights
in a semiring, unary potentials $u_t(s)$ and transition potentials $\tau_t(s, s')$ given the
observation stream $x$, the unnormalized weight of a label path $z = (z_0, \dots, z_t)$ is

$$w_t(z) = u_0(z_0) \prod_{i=1}^{t} \tau_{i-1}(z_{i-1}, z_i)\, u_i(z_i),$$

with the factors multiplied from left to right in increasing order of $i$.
