# The toric coordinates lie in the kernel of the structural theta map

Let $p$ be a prime,
$K$ a base field (`BaseField p`) with base realization $B$, $X$ an analytic space over $B$ with a
point realization $P$, $S$ a period source of $X$ (`Source`), $\Omega$ a differential source,
`AΩ` an absolute form source and $C$ a toric chart of the absolute forms with the differential of
`AΩ`. Assume that presheaves of commutative rings and of abelian groups on the étale and
pro-étale sites of $X$ have sheafifications, that sheafification of abelian-group presheaves
inverts exactly the locally bijective maps, that the inclusion of the étale site into the
pro-étale site is continuous with right-adjoint pushforwards of ring sheaves and of module
sheaves, and that the canonical map from the inverse image of the constant étale sheaf $W(k)$,
for $k$ the residue field of $K$, to the constant pro-étale sheaf $W(k)$ is an isomorphism. Then
for each coordinate index $i$ of $C$, the element $u_i = T_i - [T_i^\flat]$
(`ToricChart.infCoordinate`) of the naive structural ring $\mathcal{O}B_{\inf}$ at the boundary of
$C$, the difference of the chart's original coordinate $T_i$ and the Teichmüller lift of its tilt
root $T_i^\flat$, is sent to $0$ by the structural theta map
$\theta : \mathcal{O}B_{\inf} \to \widehat{\mathcal{O}}$.
