# Alternation of equilibrium indices along isoclines

**Setting.** Two species with densities $x,y\ge0$ follow the Kolmogorov system

$$\dot x=x\,f(x,y),\qquad \dot y=y\,g(x,y)$$

on $\mathbb{R}_+^2$, where the per capita growth rates $f,g$ need not have fixed interaction signs (the sign of $\partial f/\partial y$ or $\partial g/\partial x$ may switch from mutualistic to parasitic with density). Let $\Gamma_f=\{f=0\}$ and $\Gamma_g=\{g=0\}$ be the nontrivial isoclines in $\mathbb{R}_+^2$. Hypotheses: (H1) each of $\Gamma_f,\Gamma_g$ is a single nonempty continuous curve; (H2) $f$ (resp. $g$) has strict constant sign on each side of $\Gamma_f$ (resp. $\Gamma_g$) and changes sign across it; (H3) no more than two isoclines meet at a point (so $(0,0)\notin\Gamma_f\cup\Gamma_g$); (H4) isoclines cross transversally at equilibria, with no tangencies and no coincident arcs.

**Theorem.** Under (H1)-(H4) with $f,g$ continuous, the equilibria in the open quadrant $\{x>0,y>0\}$ (the points of $\Gamma_f\cap\Gamma_g$), taken in order along either isocline, alternate between Poincare index $+1$ and index $-1$. The alternation extends to equilibria on the coordinate axes other than the origin.

**Corollaries ($C^1$ case).**

- If $\partial f/\partial x<0$ and $\partial g/\partial y<0$ (intraspecific competition), the interior equilibria alternate between attractive equilibria and saddles along the isoclines; a nonzero equilibrium on an axis is unique on that axis and is attractive when its index is $+1$.
- If $\partial f/\partial x>0$ and $\partial g/\partial y>0$ (positive intraspecific density dependence, e.g. Allee effects), the interior equilibria alternate between repulsive equilibria and saddles; an equilibrium on an axis is unique there and is repulsive when its index is $+1$.

## Expansion

At a transversal crossing of $\Gamma_f$ and $\Gamma_g$, the index is the sign of the Jacobian determinant of $(f,g)$, i.e. $+1$ or $-1$ according to whether the ordered pair of curves crosses with positive or negative orientation. Walking along $\Gamma_f$, the sign of $g$ flips at each crossing of $\Gamma_g$ (H2), so consecutive crossings have opposite orientation and hence opposite index. With same-sign self-regulation the trace $xf_x+yg_y$ at an interior equilibrium has a fixed sign, so index $+1$ points are nodes or foci of the stability fixed by that sign. Ecologically, two stable states along an isocline (for example stable coexistence and a stable single-species state) must be separated by a saddle acting as a threshold, independently of the functional forms chosen for $f$ and $g$.

## Sources

- Chloe Mian, Sylvain Billiard, Violaine Llaurens, Charline Smadi, "Dynamics of Two Species with Density-Dependent Interactions and Application to Mutualism", *Bulletin of Mathematical Biology* 88(9) (2026), 152, Theorem 3.1, Proposition 3.5 and Corollaries 3.7, 3.9, 3.10, 3.11 (Section 3); hypotheses 1-4 in Section 3.1, <https://doi.org/10.1007/s11538-026-01724-1> (preprint arXiv:2509.06062).
