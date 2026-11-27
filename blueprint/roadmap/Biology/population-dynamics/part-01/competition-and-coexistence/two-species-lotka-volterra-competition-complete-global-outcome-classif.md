# Global outcomes of two-species Lotka–Volterra competition

For the competitive Lotka–Volterra equations $\dot x_1 = r_1 x_1 (1 - (x_1 + \alpha_{12} x_2)/K_1)$ and $\dot x_2 = r_2 x_2 (1 - (x_2 + \alpha_{21} x_1)/K_2)$ with positive parameters (Hofbauer and Sigmund 1998, Sec. 3.3), on the open quadrant, the generic outcomes are determined by comparing $\alpha_{12}$ with $K_1/K_2$ and $\alpha_{21}$ with $K_2/K_1$: (i) if $\alpha_{12} < K_1/K_2$ and $\alpha_{21} < K_2/K_1$, the interior equilibrium exists and attracts every interior orbit; (ii) if $\alpha_{12} > K_1/K_2$ and $\alpha_{21} > K_2/K_1$, the interior equilibrium is a saddle whose stable manifold separates the basins of $(K_1, 0)$ and $(0, K_2)$; (iii) if $\alpha_{12} < K_1/K_2$ and $\alpha_{21} > K_2/K_1$, every interior orbit tends to $(K_1, 0)$; (iv) in the reverse case every interior orbit tends to $(0, K_2)$. The derivation: the nullclines $x_1 + \alpha_{12} x_2 = K_1$ and $x_2 + \alpha_{21} x_1 = K_2$ are lines whose relative position is fixed by the two comparisons; orbits are bounded; the Dulac function $1/(x_1 x_2)$ turns the vector field into one with divergence $-r_1/K_1 \cdot 1/x_2 - r_2/K_2 \cdot 1/x_1 < 0$, so there are no periodic orbits; and every bounded interior orbit therefore converges to an equilibrium by the [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md), which the signs of the vector field in the regions bounded by the nullclines identify in each case.

## Depends on

- [Generalized Lotka–Volterra vector field](../../replicator-and-lotka-volterra-equivalence/lv-field.md)

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

1. The model, invariance of the closed quadrant, boundedness, and the equilibria.
2. The nullclines and the sign of the vector field in the regions they bound.
3. Absence of periodic orbits by the Dulac function $1/(x_1 x_2)$, and the global conclusions by Poincaré–Bendixson.
4. The saddle and its stable manifold in case (ii); the non-generic equality cases, and the complete classification for all sign patterns (Bomze, through the equivalence with the three-type replicator equation), as separate statements.

## Sources

- J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge University Press, 1998, Sec. 3.3. <https://doi.org/10.1017/CBO9781139173179>
- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Theorem 3. <https://doi.org/10.1090/S0273-0979-03-00988-1>
