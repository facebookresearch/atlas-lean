# Maximal total population and origin instability in the two-patch logistic model

**Model.** After rescaling patch 1 to unit growth rate and carrying capacity, two logistic subpopulations coupled by symmetric dispersal at rate $D\ge0$ satisfy

$$\dot x_1=x_1(1-x_1)+D(x_2-x_1),\qquad \dot x_2=rx_2\Big(1-\frac{x_2}k\Big)+D(x_1-x_2),$$

with relative growth rate $r>0$ and relative carrying capacity $k>0$ of patch 2.

**Theorem (global dynamics).** There are no periodic orbits, and a coexistence equilibrium $P_3=(\bar x_1(D),\bar x_2(D))$ in the open first quadrant is globally asymptotically stable there. If $D<r/(1+r)$ the origin is a repeller and infinitely many heteroclinic orbits join it to $P_3$; if $D>r/(1+r)$ the origin is a saddle and there is a unique heteroclinic connection (its unstable manifold) from the origin to $P_3$.

**Theorem (optimal dispersal).** Assume $k\ne1$ (for $k=1$, $(1,1)$ is an equilibrium for every $D$, so $\Omega\equiv1+k$). The total equilibrium population $\Omega(D)=\bar x_1(D)+\bar x_2(D)$ satisfies the bound

$$\Omega(D)\le\Omega^*=\frac12\Big(\sqrt{1+\tfrac{r^2+1}{r}k+k^2}+(1+k)\Big),$$

where $\Omega^*$ is the maximum of $\bar x_1+\bar x_2$ along the curve of equilibria continued to all real $D$; it is attained at some $D^*\in\mathbb R$, which may be negative, so $\Omega^*$ need not be a value of $\Omega$ on $D\ge0$ (for $r=2$, $k=1/2$, $\Omega$ decreases from $\Omega(0)=1.5$ while $\Omega^*\approx1.541$). With $k^*(r)=\dfrac{r(3+r)}{1+3r}$, the maximizer satisfies $D^*>0$, so that $\Omega^*$ is attained at a positive dispersal rate, exactly if $r>1$ and $k>k^*(r)$, or $r<1$ and $k<k^*(r)$; if $r<1$ and $k^*(r)<k<1$, or $r>1$ and $1<k<k^*(r)$, then $\Omega'(D)>0$ for all $D>0$; in all other cases (with $k\ne1$) dispersal reduces the total population, $\Omega(D)<1+k$ for $D>0$. The case $r>1$, $1<k<k^*(r)$ is the image of the case $r<1$, $k^*(r)<k<1$ under exchanging the patches, $(r,k,D)\mapsto(1/r,1/k,D/r)$ (note $k^*(1/r)=1/k^*(r)$); Corollary 4.5 of the source omits it, e.g. for $r=2$, $k=1.2$ one has $\Omega(0)=2.2<\Omega(1)\approx2.234<\Omega(50)\approx2.250$.

## Expansion

The Jacobian at the origin is $\begin{pmatrix}1-D&D\\D&r-D\end{pmatrix}$, whose determinant $(1-D)(r-D)-D^2=r-D(1+r)$ changes sign at $D=r/(1+r)$: below this threshold both eigenvalues are positive and orbits leave the origin almost parallel to the axes, so a small population can stay near one axis (one patch nearly empty) for a long time; above it, the origin becomes a saddle, orbits are funnelled onto its one-dimensional unstable manifold, which runs through the interior, and both patches grow together. Under demographic noise this makes stochastic extinction of a subpopulation less likely, so stronger dispersal increases metapopulation resilience even when it lowers the equilibrium total. The bound $\Omega^*$ comes from eliminating $D$ between the equilibrium equations, giving an explicit curve of equilibria parametrized by $\bar x_1$, and maximizing $\bar x_1+\bar x_2$ along it; the classical observation that asymmetric patches let dispersal raise the total population above $1+k$ is recovered with explicit thresholds.

## Sources

- Marc Jorba-Cuscó, Ruth I. Oliva-Zúniga, Josep Sardanyés and Daniel Pérez-Palau, "Optimal dispersal and diffusion-enhanced robustness in two-patch metapopulations: origin’s saddle-source nature matters", Theory in Biosciences 143 (2024), 79–95, <https://doi.org/10.1007/s12064-023-00411-2>; numbering as in arXiv:2308.01364: Section 2 (model and Theorem 2.4) and Section 4 (Theorem 4.4, Corollary 4.5).
