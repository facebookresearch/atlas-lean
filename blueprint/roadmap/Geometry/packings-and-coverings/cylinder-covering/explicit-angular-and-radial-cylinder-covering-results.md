# Explicit angular, ruled and radial cylinder-covering results

Write $H=\sqrt2$, $p(x,y,t)=(x,y,Ht)$ and $K=\{p(x,y,t):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$. If $u$ is a unit axis, let $A_K(u)$ be the Euclidean-normalized two-dimensional Hausdorff area of the orthogonal shadow of $K$ on $u^\perp$ and $A_{\min}=\inf_u A_K(u)$. A cylinder with axis $u$ and base $B\subset u^\perp$ is $B+\mathbb R u$. Its area cost is $|B|$ and its relative cost is $|B|/A_K(u)$. A triangular base is the compact, convex, measurable hull of three affinely independent points, with finite area, in the perpendicular plane of a unit axis.

**Angular families.** Use the tetrahedron and costs just defined. For $0<\varepsilon\le1$, divide $[-1,1]$ into $n=\lceil2/\varepsilon^2\rceil$ equal intervals $[a,b]$. For each interval put $\alpha=(1+ab)/4$, $\beta=(a+b)/4$, $d(q)=q^2(1+q^2)/16$, and $T=1/2+\varepsilon^2(1/1000+\max(d(a),d(b)))$. The lower cylinder axis is the unit normalization of $(1,\varepsilon\alpha,H\varepsilon\beta)$, and its base is the perpendicular projection of the triangle with vertices $p(0,0,0),p(0,aT,T),p(0,bT,T)$. The upper axis is the normalization of $(-\varepsilon\alpha,1,H\varepsilon\beta)$ and its base is the perpendicular projection of the triangle with vertices $p(0,0,1),p(aT,0,1-T),p(bT,0,1-T)$. Their total area divided by $H$ is the sum over intervals of $(b-a)T^2/\sqrt{1+\varepsilon^2(\alpha^2+2\beta^2)}$, and differs from $1/2-(13/6000)\varepsilon^2$ by at most $2\varepsilon^4$. In addition $A_{\min}=H$, and for $0<\varepsilon\le1/2000$ the stated family covers $K$ and has both total area below $A_{\min}/2$ and total relative cost below $1/2$.

For a compact planar label set $D$, a planar field $v$, and $L>0$, set

$$S(D,v,L)=\{(p_1+sv_1(p),p_2+sv_2(p),s):p\in D,\ |s|\le L\},$$

$$S_h(D,v,L)=\{(s,p_1+sv_1(p),h(p_2+sv_2(p))):p\in D,\ |s|\le L\}.$$

Write $w_h(v)=(1+v_1^2+h^2v_2^2)^{-1/2}$. The hyperbolic derivative condition at length $L$ is that $Dv(p)$ has real eigenvalues $\lambda_p,-\lambda_p$ with $0<L\lambda_p<1$ at every label. In what follows, a finite cover of a set means pointwise containment in the union; the cost is the sum of perpendicular-base areas, measured in their Euclidean planes. A parallelogram is a nondegenerate closed affine image of $[0,1]^2$. An open bounded base is open in its perpendicular plane, bounded and measurable.

**Hyperbolic ruled approximation.** When $D$ is compact and $v$ is $C^1$ on an open neighborhood of $D$ and satisfies the hyperbolic condition at $L>0$, $S(D,v,L)$ has a finite parallelogram-cylinder cover of cost at most $\int_D w_1(v(p))\,dp+\epsilon$ for every $\epsilon>0$. No hypothesis on the boundary of $D$ is needed.

**Square-zero ruled approximation.** Let $D$ be compact and $G$ of class $C^1$ on a neighborhood, with $DG(p)^2=0$ at every label. For all $h,\epsilon>0$ there are finitely many nondegenerate translated, scaled, rotated closed square tiles $T_i$ and slopes $g_i\in\mathbb R^2$ whose auxiliary cylinders $U_i=\{(s,b+sg_i):s\in\mathbb R,\ b\in T_i\}$ cover $S_1(D,G,1)$, with

$$\sum_i |T_i| w_h(g_i)\le\int_D w_h(G(p))\,dp+\epsilon.$$

For every $a\in\mathbb R$, their images under $(x,y,z)\mapsto(x,y,hz)$ and $(x,y,z)\mapsto(y,x,h(a-z))$ are exactly the carriers of two families of parallelogram cylinders, both of area $h|T_i|w_h(g_i)$ for each $i$. The same tiles and slopes are chosen before $a$.

**Regular tetrahedra.** For every convex hull of four affinely independent equidistant vertices of positive edge length, there is a finite parallelogram-cylinder cover with total area below half the minimum shadow area and total relative cost less than $1/2$. There is also such a cover with open bounded bases (a separate witness). Cost is measured using the shadows of the same tetrahedron in each cylinder’s own direction.

**Radial sweeps.** Let $e$ be a unit normal and $a,b\in e^\perp$ independent, with $p_0\in e^\perp$. On $[\alpha,\beta]$ with $\alpha<\beta$, assume continuous $R\ge0$, continuous scalar $\lambda$, and a continuous field $w$ in $e^\perp$ of within-interval derivative $w'(t)=\lambda(t)(a+tb)$. For $L>0$ sweep points $p_0+\rho(a+tb)+s(e+w(t))$ over $0\le\rho\le R(t)$ and $|s|\le L$. Let $\kappa=\sqrt{\|a\|^2\|b\|^2-\langle a,b\rangle^2}$ and $I=\kappa\int_\alpha^\beta R(t)^2/(2\sqrt{1+\|w(t)\|^2})\,dt$.

For every choice of tags in all equal $N$-partitions, one cylinder per cell with unit axis $\widehat{e+w(\mathrm{tag})}$ covers the sweep for every $N>0$. Explicit bases are projections of the following triangles in the affine coordinates $p_0+xa+yb$. With cell width $\Delta$, midpoint $u$, cap maximum $R_i$, $d=L\sup|\lambda|$ and $c=3d+1$, use vertices $(l,ul)$ and $(r,ur\pm\Delta(r-l)/2)$ where $l=-c\Delta$, $r=R_i+d\Delta$. Each base has area $\kappa\Delta(R_i+(d+c)\Delta)^2/(2\sqrt{1+\|w(\mathrm{tag})\|^2})$, and the total tends to $I$.

If instead each base is the projection of the portion of the actual sweep in that cell, it is compact, measurable, finite-area, perpendicular to the same axis and contained in the triangular base. These actual cylinders cover the sweep for every $N>0$; their total cost is eventually at most $I+\epsilon$ for every $\epsilon>0$ and has limsup at most $I$. No convergence to $I$ from below is asserted for the actual bases.

## Depends on

- Unified perpendicular-plane bases and Hausdorff area comparison, two coordinate descriptions of ruled families, tagged uniform partitions and radial sweep charts.

## Proof depends on

- Exact angular strip coverage and area error; hyperbolic and square-zero approximation; transfer to arbitrary regular tetrahedra for both base classes; radial triangle inclusion and tagged-sum convergence.

## Expansion

Split the aggregate into angular area, angular coverage, the two ruled approximation theorems, the two regular tetrahedron covers, and the two radial statements. Use the same canonical hyperbolic approximation node as the finite ruled-family result when expanding both. The radial projection formulas are per cell, while the cost conclusions range over every tag family. The component of the source that concerns a general triangular cover of every regular tetrahedron is not part of this selected conjunction.

## Sources

- OpenAI Math, [`fourPaperMain`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CylinderCovering.lean#L561-L570) (statement and local definitions).
