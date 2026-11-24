# The EM marginal of an HMM is its likelihood

For every $T$, every valid HMM $h$ and every
observation sequence $x$, the marginal at $h$ and $x$ of the EM model of HMMs with state paths
$(z_0, \dots, z_T)$, that is the sum over all such paths of the path weight of $z$ and $x$, equals
the likelihood under $h$ of the observations $x_0, \dots, x_T$.
