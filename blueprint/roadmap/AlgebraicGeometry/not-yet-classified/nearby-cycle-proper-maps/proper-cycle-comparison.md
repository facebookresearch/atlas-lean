# Proper Cycle Comparison

For a morphism $G$ from the zero fibre $A$ of $s$ on $X$ to the zero fibre $B$ of $t$ on $Y$
(maps $g$ and $g_0$ on complex points) with the given derived data, chosen functorial resolutions
$R_1$, $R_2$ of the exponential covers, and comparisons $E_1$, $E_2$ of these resolutions with the
deck translation by 1 for which the nearby monodromy fixes the specialization map (`hc₁`, `hc₂`):
an isomorphism of cycle triangles, natural in the bounded constructible complex $K$ on $X$, from
the cycle triangle of $B$ at $Rg_* K$ to the image under $Rg_{0*}$ of the cycle triangle of $A$
at $K$, whose first component is the base-change map of the zero-fibre square (through
`cycleFirstIso`), whose second component is `properNearbyComparison G` (through
`nearbyFormulaIso`) and intertwines the nearby monodromies, and whose third (vanishing-cycle)
component intertwines the vanishing monodromies. The third component is not otherwise
constrained.
