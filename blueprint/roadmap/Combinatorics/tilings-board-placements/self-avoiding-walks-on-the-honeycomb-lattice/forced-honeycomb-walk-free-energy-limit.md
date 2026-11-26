# Existence of forced honeycomb self-avoiding-walk free energy

Index honeycomb vertices by $U_{i,j},D_{i,j}$ for all integers $i,j$, with $U_{i,j}$ adjacent to $D_{i,j},D_{i-1,j},D_{i,j-1}$. Embed them in $\mathbb C$ by giving $U_{i,j}$ coordinates $(i+j/2+1/2,(j+1/3)\sqrt3/2)$ and $D_{i,j}$ coordinates $(i+j/2+1,(j+2/3)\sqrt3/2)$. For any start $o$, complex $e$ and real $s$, let $Z_n$ sum $(2+\sqrt2)^{-n/2}\exp(s\operatorname{Re}(\overline e(z(\gamma_n)-z(o))))$ over all $n$-edge self-avoiding walks $\gamma$ from $o$. Then $\log Z_n/n$ converges as $n\to\infty$ to its real filter limit. The force vector is not assumed to have unit norm, and the value at $n=0$ uses totalised division.

## Depends on

- Embedded honeycomb graph, n-edge self-avoiding walks and real directional-force partition function.

## Proof outline

Relate the endpoint-tilted enumeration to the native honeycomb walk model, handle both up and down initial vertex types at fixed force, and apply the limit result at the level of normalized logs. Do not import a small-force exponent or a moment law.

- Length concatenation bounds with start-vertex dependence controlled, positivity and finiteness, then a subadditive limit argument.

## Sources

- [Comparator statement: `OAI.HoneycombForce.logPartition_tendsto`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HoneycombFreeEnergy.lean#L64-L67)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/237.md)
