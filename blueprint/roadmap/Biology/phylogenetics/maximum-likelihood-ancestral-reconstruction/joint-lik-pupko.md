# Likelihood of Pupko's joint reconstruction

For every tree $t$ and root weights $\pi$, Pupko's [joint reconstruction](pupko.md) $(\hat s, \hat z)$ satisfies

$$\pi(\hat s)\, W(t, \hat s, \hat z) = \max_{s} \pi(s)\, M(t, s),$$

where $W$ is the [weight](../felsenstein-s-pruning-algorithm/weight.md) and $M$ the [max-product recursion](max-prune.md).
