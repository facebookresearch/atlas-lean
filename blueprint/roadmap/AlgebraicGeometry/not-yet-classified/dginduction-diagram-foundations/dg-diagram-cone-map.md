# Dg diagram cone map

For closed maps $f : M \to N$ and $g : M' \to N'$ of right DG modules over a DG category $C$
over a field $k$, with cone models $Q$ of $f$ and $Q'$ of $g$, closed maps $a : M \to M'$ and
$b : N \to N'$, and a degree $-1$ map $h : M \to N'$ with $dh = b \circ f - g \circ a$: a map from
the cone of $f$ to the cone of $g$ which, at every object of $C$ and under the identifications of
$Q$ and $Q'$ with the mapping cones of the components of $f$ and $g$ (in degree $r$, the terms
$M^{r+1} \oplus N^r$ and $(M')^{r+1} \oplus (N')^r$, with the conventions of
`CochainComplex.mappingCone`), has the blocks $a : M^{r+1} \to (M')^{r+1}$,
$h : M^{r+1} \to (N')^r$ and $b : N^r \to (N')^r$.
