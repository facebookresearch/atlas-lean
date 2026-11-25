# Expected transition count

For a valid HMM $h$, observation sequences
$x_0, \dots, x_{N-1}$ and states $s, s'$, the expected transition count is
$\sum_{n < N} \sum_{z} p_h(z \mid x_n) \, c_{s s'}(z)$, where $z$ ranges over the state paths
$(z_0, \dots, z_T)$, $p_h(z \mid x_n)$ is the posterior weight of $z$ for $x_n$, and $c_{s s'}(z)$
is the number of $t < T$ with $z_t = s$ and $z_{t+1} = s'$.
