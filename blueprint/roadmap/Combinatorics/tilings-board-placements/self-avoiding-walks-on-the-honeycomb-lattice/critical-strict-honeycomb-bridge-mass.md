# Critical mass of strict honeycomb bridges to free terminal ports

Set $B_0=1$. For each integer $h>0$ use rows $0\le j<h$ of the honeycomb graph with edges from $U_{i,j}$ to $D_{i,j},D_{i-1,j},D_{i,j-1}$ when present. Let $B_h$ be the sum in the extended nonnegative reals of $(2+\sqrt2)^{-\ell/2}$ over distinct-vertex traces from $U_{0,0}$ to any $D_{i,h-1}$, with $\ell$ the number of listed centers (no extra port weights). Then for some positive real $c,C$ and every $h\ge0$,

$$
c(1+h)^{-1/4}\le B_h\le C(1+h)^{-1/4},
$$

comparing the real bounds by their images in the extended nonnegative reals.

## Depends on

- The strict strip trace family, zero-height mass and nonnegative extended-real weight.

## Proof depends on

- [Positive-height real bridge-mass estimate (requires a trace and sum bridge)](critical-honeycomb-strip-mass-and-displacement.md)
- Critical strip mass lower and upper estimates and identification of the weights with the exact strict-bridge sum.

## Expansion

Check the solution theorem for this exact ENNReal convention and prove the trace-list/summed-terminal bridge to any reused strip result. Isolate the elementary extension to height zero. Do not promote a claim about two prescribed endpoints or concentration of their chord length.

## Sources

- [Comparator statement: `OAI.CriticalHoneycomb.finiteBridgeMassEstimate`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HoneycombBridgeMassSupport.lean#L71-L74)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/237.md)
- [Associated critical bridge mass construction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/HoneycombChords/BridgeMass.lean)
