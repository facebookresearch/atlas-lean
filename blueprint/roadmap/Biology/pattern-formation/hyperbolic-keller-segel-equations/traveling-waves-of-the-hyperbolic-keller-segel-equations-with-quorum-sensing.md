# Traveling waves of the hyperbolic Keller–Segel equations with quorum sensing

**Model.** The one-dimensional hyperbolic Keller–Segel system with quorum (logistic) sensitivity is

$$\partial_t\sigma+\partial_x\big(\sigma(1-\sigma)\partial_xS\big)=0,\qquad -\partial_{xx}S+S=\sigma,\qquad x\in\mathbb R,$$

for a cell volume fraction $\sigma\in[0,1]$ and chemical concentration $S$. Admissible weak solutions satisfy an entropy inequality $\partial_t\eta(\sigma)+\partial_x(\partial_xS\,q(\sigma))+(\sigma-S)(q-g\eta')(\sigma)\le0$ for convex entropy pairs. Consider one-sided far-field conditions, either vacuum $S(-\infty)=\sigma(-\infty)=0$ or non-vacuum $S(-\infty)=\sigma(-\infty)=\sigma_\infty\in(0,1]$.

**Jump conditions.** Along a discontinuity curve $x=x(t)$ of an entropy solution, $S$ and $\partial_xS$ are continuous, the shock speed is

$$x'(t)=\partial_xS\,(1-\sigma^+-\sigma^-),$$

and the entropy condition requires $\partial_xS\le0$ if $\sigma^+>\sigma^-$ and $\partial_xS\ge0$ if $\sigma^+<\sigma^-$.

**Theorem.** For every speed $c$ there are entropy traveling waves $\sigma(t,x)=\sigma_c(x-ct)$, $S(t,x)=S_c(x-ct)$.

1. With vacuum far field, both right-going ($c>0$) and left-going ($c<0$) waves exist, either continuous or piecewise smooth with exactly one jump. A wave with $c\ne0$ can only jump from $0$ to a positive value (then $c=(1-\sigma_c(\xi_0+))\,S_c'(\xi_0)<0$) or from a positive value to $0$ (then $c=(1-\sigma_c(\xi_0-))\,S_c'(\xi_0)>0$). After translation the continuous profiles have $\sigma_c=0$, $S_c=ce^{\xi}$ for $\xi\le0$, and for $\xi>0$ the pair $(S_c,Y_c=S_c')$ solves $S_c'=Y_c$, $Y_c'=S_c-1+c/Y_c$ with $S_c(0)=Y_c(0)=c$.
2. With non-vacuum far field $\sigma_\infty\in(0,1)$, every traveling wave profile is continuous.

The saturated case $\sigma_\infty=1$ reduces to the vacuum case via $\eta=1-\sigma$, $Q=1-S$. Nontrivial stationary solutions (e.g. $\sigma_s=0$, $S_s=A_0e^{x}$ for $x\le x_0$ and $\sigma_s=1$ for $x>x_0$, $A_0\le0$) show non-uniqueness of the far-field problem.

## Expansion

In the moving frame the continuity equation integrates once to $\sigma_c\big(c-(1-\sigma_c)S_c'\big)=\text{const}$, which vanishes under a vacuum far field, so on the support of $\sigma_c$ one has $(1-\sigma_c)S_c'=c$; inserting $\sigma_c=1-c/S_c'$ into $-S_c''+S_c=\sigma_c$ gives the planar ODE above. Rankine–Hugoniot for the flux $\sigma(1-\sigma)\partial_xS$ with continuous $\partial_xS$ gives the shock speed, and the entropy inequality selects the admissible jump direction, which rules out jumps between two positive states when $c\ne0$.

## Sources

- Xin Liu, William Kyle Barker, "The traveling wave solutions of the 1D hyperbolic Keller-Segel equations", arXiv:2608.12226 (2026), Theorems 1.1–1.2, Proposition 2.1, Propositions 4.2, 4.4, 4.7 and 4.8, <https://doi.org/10.48550/arXiv.2608.12226>.
