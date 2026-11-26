# Roberts' theorem for neutral rules

With finitely many agents, at least three outcomes and unrestricted valuations, every neutral weakly monotone social choice rule (one with $f(b \circ \pi) = \pi^{-1}(f(b))$ for every permutation $\pi$ of the outcomes and every valuation profile $b$ at which no agent values two outcomes equally, where $(b \circ \pi)_i(a) = b_i(\pi(a))$) maximizes a pure weighted welfare $\sum_i w_i b_i(a)$ with nonnegative weights summing to $1$; the additive constants vanish. Zero weights must be allowed, to cover dictatorships.

## Proof sketch

A neutral rule is onto, since permuting a profile without ties moves its outcome to any other outcome, so Roberts' theorem applies on the full range; neutrality at profiles without ties then forces the affine constants $c(a)$ to be equal across outcomes.

## Depends on

- [Affine maximizer and weighted Groves mechanism](affine-maximizer-and-weighted-groves-mechanism.md)

## Proof depends on

- [Roberts' theorem](roberts-theorem.md)

## Sources

- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
