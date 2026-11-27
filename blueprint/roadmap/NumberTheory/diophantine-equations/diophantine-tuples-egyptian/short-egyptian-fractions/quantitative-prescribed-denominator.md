# A double-logarithmic length bound for a prescribed denominator

For every real $\varepsilon>0$ there is a natural $m_\varepsilon\ge2$ such that for every natural
$m\ge m_\varepsilon$, some strictly increasing positive denominator tuple of length $k$ has
reciprocal sum $1$, contains $m$, and satisfies

$$
k\le (257/\log2+\varepsilon)\log\log m.
$$

The threshold is uniform in all $m$ above it; this is an existence upper bound, not an optimal
constant for a minimum.

## Expansion

Isolate the residue supply and the arithmetic estimates needed by the source’s composite-denominator construction. Check that a numerator of one and the exact specified denominator are recovered simultaneously, and track the constant $257/\log2$.

## Sources

- [EgyptianFractions.lean — `quantitative_marked_length`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L89-L97)
