# Critical honeycomb strip mass and horizontal displacement moment

For $N\ge1$ take the vertices $U_{i,j},D_{i,j}$ for $i\in\mathbb Z$, $0\le j<N$, with $U_{i,j}$ joined to $D_{i,j},D_{i-1,j},D_{i,j-1}$ whenever present. From $U_{0,0}$ take vertex-simple walks. Set $\rho=(2+\sqrt2)^{-1/2}$ and weight each walk by $\rho$ to the number of listed vertices, including both ends. Let $K_N(k)$ sum weights of walks ending at $U_{k,0}$ if $k\ne0$, and be zero at $k=0$. Let $L_N(k)$ sum those ending at $D_{k,N-1}$. Define $A_N=\sum_{k\in\mathbb Z}K_N(k)$, $B_N=\sum_{k\in\mathbb Z}L_N(k)$, and $M_N=\sum_{k\ge1} k K_N(k)$. The per-endpoint series and each of these three outer series are summable. For all $N\ge1$,

$$
\cos(3\pi/8)A_N+B_N=1,\qquad B_{N+1}\le B_N.
$$

In addition $M_{N+1}-M_N$ is comparable to $B_N$, $M_N$ to $N^{3/4}$ and $B_N$ to $N^{-1/4}$, each with its own positive constants uniform over every $N\ge1$ (two-sided bounds).

## Depends on

- Two-layer honeycomb neighbour relation, vertex-count fugacity and arch/bridge sums and positive-displacement moment.

## Expansion

Separate the following four inputs, each for integer width $N\ge1$:

- Summability of the individual arch and bridge weights at each displacement, both resulting kernels, and the length-weighted arch-displacement series defining $M_N$.
- The straight-strip flux identity $cA_N+B_N=1$, for the same arch and bridge masses as in the statement.
- The signed boundary flux identity on the stepped domain joining widths $N$ and $N+1$. It uses that domain's left and right arch terms and its side kernel; it is not another straight-strip identity. The proof can choose the step at position zero.
- The straight-strip arch-polynomial identity: there is a real polynomial $g$ satisfying the source's degree-$N$ monic arch problem with $M_N=NC-\eta[X^{N-1}]g$ for the source constants $C,\eta$.

Use these inputs to derive the moment increments and their comparisons. Keep monotonicity and the resulting two power comparisons in the application.

## Proof outline

Separate these prerequisites and the two power comparisons; relate adjacency and the length convention to the native walk API. Do not infer path-length laws from the horizontal-displacement moment or omit summability by using a totalized infinite sum.

## Sources

- [Comparator statement: `OAI.CriticalStrip.critical_strip_mass`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalStripMass.lean#L76-L78)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/237.md)
- [Four physical inputs and their application](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/StripMass/SidePaths.lean#L444-L457), [straight and stepped domains in the physical proof](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/StripMass/PhysicalPorts.lean#L552-L557), and [arch-polynomial identity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/StripMass/NorthMass.lean#L424-L427).
