# Permanence of pulsed Lotka-Volterra competition

**Single species.** For $a,b>0$, $\tau>0$ and $h>-1$, the pulsed logistic equation

$$\frac{dx}{dt}=x(a-bx)\ (t\ne k\tau),\qquad x(k\tau^+)=(1+h)x(k\tau^-)$$

has a unique globally asymptotically stable positive $\tau$-periodic solution $x^*$ when $a\tau+\ln(1+h)>0$, and every positive solution tends to $0$ when $a\tau+\ln(1+h)<0$. Along $x^*$,

$$\int_0^\tau (a-bx^*(t))\,dt=-\ln(1+h),\qquad \int_0^\tau x^*(t)\,dt=\frac{a\tau+\ln(1+h)}{b}.$$

**Two competitors.** For sensitive and resistant cell types $x_s,x_r$ treated every $\tau$ with survival factors $1+h_s,1+h_r$ (with $h_s,h_r>-1$),

$$\dot x_s=x_s(a_s-b_{ss}x_s-b_{sr}x_r),\qquad \dot x_r=x_r(a_r-b_{rs}x_s-b_{rr}x_r),\qquad x_i(k\tau^+)=(1+h_i)x_i(k\tau^-),$$

with all $a_i,b_{ij}>0$. Write $g_i=a_i\tau+\ln(1+h_i)$ for the net growth of species $i$ over one period at low density.

**Theorem.** If $g_s>0$, $g_r>0$ and

$$g_s>g_r\,\frac{b_{sr}}{b_{rr}},\qquad g_r>g_s\,\frac{b_{rs}}{b_{ss}},$$

then the pulsed competition system is robustly permanent.

## Depends on

- [Average-growth criterion for permanence under periodic pulses](average-growth-criterion-for-permanence-under-periodic-pulses.md)
- [Explicit solution of the logistic equation](../logistic-growth-equation/logistic.md)

## Expansion

The boundary attractor of the stroboscopic map splits into the origin and the two single-species periodic orbits. At the origin both species invade because $g_i>0$. On the orbit $x_r^*$ of the resistant type, the average growth of the sensitive type over a period is $g_s-b_{sr}\int_0^\tau x_r^*\,dt=g_s-b_{sr}g_r/b_{rr}$ by the periodic-integral identity, and symmetrically on $x_s^*$; the displayed inequalities say both invasion rates are positive. The average-growth criterion then gives permanence and its robustness. This recovers, by a different route, the permanence result of Jin and coauthors for pulsed competition; in the treatment reading, the inequalities say each cell type can invade the treated steady cycle of the other, so maintenance therapy keeps both in check without eliminating either.

## Sources

- Eleanor Courcelle, Jane Shaw MacDonald, Swati Patel, "Persistence of n-Species Lotka-Volterra Models with Periodic Pulses", arXiv:2609.09343 (2026), Lemma 4.1 (quoted from Jin et al.), Lemma 4.2 and Theorem 4.3 (Section 4.1), <https://doi.org/10.48550/arXiv.2609.09343>
