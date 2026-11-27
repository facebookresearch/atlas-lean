# Pupko's reconstruction is a joint maximum-likelihood reconstruction

Let $\mathrm{obs}(l, s) \ge 0$ for all $l, s$, let the tree $t$ have [nonnegative weights](nonneg-weights.md), and let $\pi(s) \ge 0$ for every $s$. Then for every root state $s$ and every [labeling](../felsenstein-s-pruning-algorithm/labeling.md) $z$,

$$\pi(s)\, W(t, s, z) \le \pi(\hat s)\, W(t, \hat s, \hat z),$$

where $(\hat s, \hat z)$ is Pupko's [joint reconstruction](pupko.md) and $W$ the [weight](../felsenstein-s-pruning-algorithm/weight.md) (Pupko et al. 2000).

## Sources

- T. Pupko, I. Pe'er, R. Shamir and D. Graur, *A fast algorithm for joint reconstruction of ancestral amino acid sequences*, Mol. Biol. Evol. 17 (2000), 890–896.
