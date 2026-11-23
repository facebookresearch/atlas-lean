# ChromHMM joint weight of a state path and mark vectors

For a natural number $T$, a [valid parameter](valid.md) $\theta$, a sequence of mark vectors $x_0, x_1, \dots$ and a state path $z = (z_0, \dots, z_T)$, the joint weight is

$$p_\theta(x, z) = \pi(z_0) \prod_{t=0}^{T-1} a(z_t, z_{t+1}) \prod_{t=0}^{T} B_{p_{z_t}}(x_t).$$
