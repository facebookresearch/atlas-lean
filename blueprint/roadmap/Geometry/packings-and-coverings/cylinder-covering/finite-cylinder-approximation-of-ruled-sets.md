# Finite cylinder approximation of ruled families

For a compact planar label set $D$, a planar field $v$, and $L>0$, set

$$S(D,v,L)=\{(p_1+sv_1(p),p_2+sv_2(p),s):p\in D,\ |s|\le L\},$$

$$S_h(D,v,L)=\{(s,p_1+sv_1(p),h(p_2+sv_2(p))):p\in D,\ |s|\le L\}.$$

Write $w_h(v)=(1+v_1^2+h^2v_2^2)^{-1/2}$. The hyperbolic derivative condition at length $L$ is that $Dv(p)$ has real eigenvalues $\lambda_p,-\lambda_p$ with $0<L\lambda_p<1$ at every label. In what follows, a finite cover of a set means pointwise containment in the union; the cost is the sum of perpendicular-base areas, measured in their Euclidean planes. A parallelogram is a nondegenerate closed affine image of $[0,1]^2$. An open bounded base is open in its perpendicular plane, bounded and measurable.

**Hyperbolic ruled approximation.** When $D$ is compact and $v$ is $C^1$ on an open neighborhood of $D$ and satisfies the hyperbolic condition at $L>0$, $S(D,v,L)$ has a finite parallelogram-cylinder cover of cost at most $\int_D w_1(v(p))\,dp+\epsilon$ for every $\epsilon>0$. No hypothesis on the boundary of $D$ is needed.

**Physical hyperbolic case.** Under the same hypotheses with $h>0$, for every isometry $F$ of three-space and $\epsilon>0$, $F(S_h(D,v,L))$ has a parallelogram cover of cost at most $h\int_D w_h(v(p))\,dp+\epsilon$.

**Other hyperbolic estimates.** In the logarithmic case let $X,k>0$, $D$ be compact with null boundary, and $v$ be $C^2$ on an open coordinate rectangle containing $D$, with $\operatorname{tr}(Dv)=0$, $\det Dv<0$ and $kX\sqrt{-\det Dv}<1$ on $D$. Then $S_1(D,kv,X)$ has an open bounded base cover of cost at most $\int_D w_1(kv(p))\,dp+\epsilon$. In the product-cell case with compact null-boundary $D$, $C^1$ field near $D$, $h,M>0$ and the hyperbolic condition at length $M$, an open bounded base cover of $S_h(D,v,M)$ costs at most $h\int_D w_h(v(p))\,dp+\epsilon$. In the orthogonal-grid case with compact null-boundary $D$ and $C^1$ field near $D$, trace zero, strictly negative determinant and $\|Dv\|\le\kappa<1$ on $D$, $S_H(D,v,1)$ has a parallelogram cover of cost at most $H\int_D w_H(v(p))\,dp+\epsilon$ for $H=\sqrt2$. In each case $\epsilon>0$ is arbitrary.

**Square-zero ruled approximation.** Let $D$ be compact and $G$ of class $C^\infty$ on a neighborhood, with $DG(p)^2=0$ at every label. For all $h,\epsilon>0$ there are finitely many nondegenerate translated, scaled, rotated closed square tiles $T_i$ and slopes $g_i\in\mathbb R^2$ whose auxiliary cylinders $U_i=\{(s,b+sg_i):s\in\mathbb R,\ b\in T_i\}$ cover $S_1(D,G,1)$, with

$$\sum_i |T_i| w_h(g_i)\le\int_D w_h(G(p))\,dp+\epsilon.$$

For every $a\in\mathbb R$, their images under $(x,y,z)\mapsto(x,y,hz)$ and $(x,y,z)\mapsto(y,x,h(a-z))$ are exactly the carriers of two families of parallelogram cylinders, both of area $h|T_i|w_h(g_i)$ for each $i$. The same tiles and slopes are chosen before $a$.

**Singular case.** For $1<p<(\sqrt{51}-5)/2$ and $1<\gamma<1/(2-p)$, write $H=\sqrt2$, $d=c^\gamma$, and in label coordinates $b=(u,v)$ put

$$F_p(b)=\left(\tfrac14(2v)^{p-1}[p+(2-p)(u/v)^2],\ (2v)^{p-2}u\right),\quad Q_p(u)=u^2[p/4+(2-p)u^2].$$

For $c>0$, set $D_c=\{d\le v\le2,\ |u|\le v,\ v\le1/2+c^2Q_p(u)+c^{5/2}\}$. Define $I_c=H\int_{D_c}w_H(cF_p)\,db$ and $B_p=(1/2)^4(2p^2+10p-13)/(30p)$. Then $B_p<0$ and $2I_c+8Hd^2=H/2+2HB_pc^2+o(c^2)$ as $c\downarrow0$.

For all sufficiently small $c>0$ there are two finite parallelogram-cylinder families and two individual triangular cylinders. The first family covers $S_H(D_c,cF_p,1)$; the second covers $(u-csF_{p,1}(b),s,H(1-v+csF_{p,2}(b)))$ for $b\in D_c$, $|s|\le1$. The two other carriers are exactly the two infinite tip cylinders, containing the corresponding bounded portions of the edge-2 tetrahedron: $(x,y,Ht)$ with $0\le t\le2d$, $|y|\le t$ and unrestricted $x$, and $(x,y,H(1-s))$ with $0\le s\le2d$, $|x|\le s$ and unrestricted $y$. Their combined four families cover the tetrahedron $K$ from the angular problem, with total area strictly below $H/2$.

## Depends on

- Perpendicular area, Euclidean isometries, smooth fields on label neighborhoods and scaled ruled sets, and right-hand asymptotics on the singular labels.

## Proof depends on

- Derive the hyperbolic, logarithmic, product-cell, grid, and square-zero cover constructions; bound the singular truncated integral and cover the two tips at the claimed cost.

## Expansion

Develop a shared model for the ruled endpoints and split the seven selected clauses. Use one canonical node on expansion for the hyperbolic claim shared with the angular-and-radial aggregate, while its nilpotent clause assumes only $C^1$ and is not the same as the smooth nilpotent clause here.

## Sources

- OpenAI Math, [`fullMain`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RuledCovering.lean#L215-L217) (statement and local definitions).
