# Brute-force likelihood given the root state

For a commutative semiring $R$, a finite state set $S$, leaf weights $\mathrm{obs}$, a [tree](tree.md) $t$ and a root state $s$, the brute-force likelihood is

$$\Lambda(t, s) = \sum_{z} W(t, s, z),$$

the sum over all [labelings](labeling.md) $z$ of $t$ of their [weights](weight.md).
