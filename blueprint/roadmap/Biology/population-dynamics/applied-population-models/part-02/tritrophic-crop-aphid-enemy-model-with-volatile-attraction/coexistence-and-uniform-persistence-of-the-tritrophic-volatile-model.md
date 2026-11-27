# Coexistence equilibrium and uniform persistence of the tritrophic model with volatile attraction

Consider crops $x$, aphids $y$ and aphid natural enemies $z$ governed by

$$
\begin{aligned}
\dot x&=rx\Big(1-\frac xK\Big)-a\frac{xy}{h+x},\\
\dot y&=y\Big(ae\frac{x}{h+x}-m-p\frac{z}{l+y}\Big),\\
\dot z&=x\Big(b+c\frac{y}{k+y}\Big)+z\Big(pq\frac{y}{l+y}-n\Big),
\end{aligned}
$$

where $r,K$ are the crop growth rate and carrying capacity, $a$ the maximal consumption rate of crop by aphids, $e$ and $q$ conversion yields, $m$ and $n$ the aphid and enemy mortality rates, $p$ the maximal uptake of aphids by enemies, $h,k,l$ half-saturation constants, $b\ge0$ the baseline attraction of enemies by crop volatile organic compounds (VOCs) and $c\ge0$ the extra attraction by VOCs released under aphid attack; all other parameters are positive. Solutions starting in $\mathbb R^3_+$ stay positive and enter the bounded region $\{x\le K_1,\ ex+y+z/q\le(er+\tfrac{b+c}{q}+1)K_1/\delta\}$ with $\delta=\min\{1/e,m,n\}$, $K_1=\max\{x_0,K\}$.

**Coexistence equilibrium.** An interior equilibrium $E^*=(x^*,y^*,z^*)$ satisfies

$$
y^*=\frac1a\,r\Big(1-\frac{x^*}{K}\Big)(h+x^*),\qquad z^*=\frac{l+y^*}{p}\Big(ae\frac{x^*}{h+x^*}-m\Big),
$$

with $x^*$ a root of the function $H(x)$ obtained by substituting these expressions into the right-hand side of the $z$-equation. Both components are nonnegative exactly when $ae>m$ and $\frac{mh}{ae-m}\le x^*\le K$. Since $H\big(\frac{mh}{ae-m}\big)>0$ and $H(K)=bK-\frac{ln}{p}\big(\frac{aeK}{h+K}-m\big)$, if

$$
ae>m\quad\text{and}\quad\frac{aeK}{h+K}\ge m+\frac{bKp}{ln},
$$

then $H$ has a zero in $\big[\frac{mh}{ae-m},K\big]$ and a coexistence equilibrium exists.

**Theorem (uniform persistence).** If $\dfrac{aeK}{h+K}>\dfrac{pbK}{nl}+m$, the system is uniformly persistent: there is $\eta>0$ such that every solution with positive initial data satisfies $\liminf_{t\to\infty}x(t),y(t),z(t)\ge\eta$.

**Theorem (global stability).** If, besides the persistence condition, there are $\alpha,\beta,\zeta>0$ making an explicit bound on the Lozinskiĭ measure (for the weighted max-norm $\max\{\alpha|z_1|,\beta|z_2|,\zeta|z_3|\}$) of the second additive compound of the Jacobian negative on the absorbing set (condition H1 in the source), then the coexistence equilibrium $E^*$ is globally asymptotically stable.

## Expansion

The persistence condition is the reverse of the stability condition of the [aphid-free equilibrium](aphid-free-equilibrium-threshold-and-transcritical-bifurcation.md): when aphids can invade $E_1$, no boundary equilibrium attracts interior orbits. The proof uses the absorbing bounded region and the Butler–McGehee lemma: if $E_0$ or the saddle $E_1$ belonged to the omega-limit set of an interior orbit, that omega-limit set would contain another point of the equilibrium's stable set (the plane $x=0$, resp. $y=0$), and the phase portraits of the boundary subsystems show that the orbit of such a point is unbounded or comes from $E_0$, contradicting boundedness. Persistence then provides the compact absorbing set required by the Li–Muldowney high-dimensional Bendixson criterion, whose negative Lozinskiĭ-measure condition excludes nonconstant periodic orbits and yields global stability.

## Depends on

- [Aphid-free equilibrium threshold and transcritical bifurcation in a tritrophic model with volatile attraction](aphid-free-equilibrium-threshold-and-transcritical-bifurcation.md)

## Sources

- Arturo J. Nic May, Eric J. Avila Vales. *Dynamics of tritrophic interaction with volatile compounds in plants* (2020), Sections 2–5: Lemmas 1–2, Section 4.1 (equilibria) and Theorems 1–3, 5–8. <https://doi.org/10.48550/arXiv.2003.07941>
