# Equilibrium dynamics of the generalized Beverton–Holt competition model with Allee effects

**Model.** Two competing species with densities $x_t, y_t \ge 0$ evolve by

$$x_{t+1} = \frac{r_1x_t^{\delta_1}}{1 + x_t^{\delta_1} + b_1y_t^{\delta_3}}, \qquad y_{t+1} = \frac{r_2y_t^{\delta_2}}{1 + y_t^{\delta_2} + b_2x_t^{\delta_4}},$$

with all parameters positive: $r_i$ maximal growth, $b_i$ relative interspecific competition, $\delta_1,\delta_2$ the nonlinearity (intensity) of intraspecific competition and $\delta_3,\delta_4$ that of interspecific competition. Condition **H1** is $\delta_i > 1$ and $r_i > \delta_i(\delta_i-1)^{1/\delta_i - 1}$ for $i = 1,2$: each species alone has a strong Allee effect with threshold $A_i$ and carrying capacity $K_i$.

**Theorem.**

1. (Dissipativity and boundary attractors.) $\mathbb R^2_+$ is forward invariant and $[0,r_1]\times[0,r_2]$ is absorbing. Under H1 there are five boundary equilibria $(0,0), (A_1,0), (K_1,0), (0,A_2), (0,K_2)$; $(0,0)$, $(K_1,0)$ and $(0,K_2)$ are locally asymptotically stable and $(A_1,0), (0,A_2)$ are saddles.
2. (Intraspecific dominance gives equilibrium dynamics.) If $\delta_1\delta_2 \ge \delta_3\delta_4$, the map is strongly competitive on the interior of $\mathbb R^2_+$ and every orbit in $\mathbb R^2_+$ converges to an equilibrium.
3. If $\delta_1\delta_2 < \delta_3\delta_4$ but

$$r_1 < \Big(\frac{\delta_1\delta_2}{b_2(\delta_3\delta_4 - \delta_1\delta_2)}\Big)^{1/\delta_4} \quad\text{or}\quad r_2 < \Big(\frac{\delta_1\delta_2}{b_1(\delta_3\delta_4 - \delta_1\delta_2)}\Big)^{1/\delta_3},$$

every orbit still converges to an equilibrium.
4. (Interior equilibria.) Under H1 let $F_1(x) = \big((r_1x^{\delta_1-1} - x^{\delta_1} - 1)/b_1\big)^{1/\delta_3}$, $F_2(y) = \big((r_2y^{\delta_2-1} - y^{\delta_2} - 1)/b_2\big)^{1/\delta_4}$, $x_c = r_1(\delta_1-1)/\delta_1$, $y_c = r_2(\delta_2-1)/\delta_2$. If $F_1(x_c) < A_2$ or $F_2(y_c) < A_1$ there is no interior equilibrium; if $A_2 < F_1(x_c) < K_2$ and $K_1 < F_2(y_c)$, or $A_1 < F_2(y_c) < K_1$ and $K_2 < F_1(x_c)$, there are two; if $F_1(x_c) > K_2$ and $F_2(y_c) > K_1$, there are four.

## Depends on

- [Allee threshold of the sigmoid Beverton–Holt model](allee-threshold-of-the-sigmoid-beverton-holt-model.md)

## Expansion

With the order $(x,y)\le_K(x',y')$ iff $x\le x'$ and $y\ge y'$, a planar map is competitive when its Jacobian has nonnegative diagonal and nonpositive off-diagonal entries; for this map the diagonal entries are positive and the off-diagonal ones negative, and the proof shows that under $\delta_1\delta_2\ge\delta_3\delta_4$ (or the smallness conditions on $r_i$ of item 3) the map is moreover injective with Jacobian determinant positive, hence strongly competitive. Orbits of such planar maps are eventually componentwise monotone, hence converge to equilibria. Interior equilibria are intersections of the nullclines $y = F_1(x)$ and $x = F_2(y)$, each a hump peaking at $x_c$ (resp. $y_c$); comparing the hump heights with the single-species thresholds and capacities counts the crossings.

## Sources

- Yun Kang, "Dynamics of a generalized Beverton–Holt competition model subject to Allee effects", arXiv (2015). Section 2.2 (model, H1), Lemma 3.1, Theorems 3.1, 3.2 and 3.5. <https://doi.org/10.48550/arXiv.1505.05913>. Published version: "Dynamics of a generalized Ricker–Beverton–Holt competition model subject to Allee effects", Journal of Difference Equations and Applications 22(5) (2016), 687–723, <https://doi.org/10.1080/10236198.2015.1135910>; locators above refer to the arXiv version.
