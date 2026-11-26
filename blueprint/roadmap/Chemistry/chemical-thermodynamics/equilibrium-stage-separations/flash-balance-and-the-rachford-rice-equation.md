# Flash balance and the Rachford–Rice equation

Let a feed of flow $F > 0$ and composition $z$ on the simplex ($z_i \ge 0$, $\sum_i z_i = 1$) split into a liquid $L$ and a vapour
$V$ in equilibrium with prescribed K-values $K_i > 0$, so that $Fz = Lx + Vy$, $F = L + V$ and $y_i = K_i x_i$, and put
$\beta = V/F$. For $\beta \in [0, 1]$ every denominator $1 + \beta(K_i - 1)$ is positive, the phase compositions are
$x_i = z_i/(1 + \beta(K_i - 1))$ and $y_i = K_i x_i$, and both sum to one if and only if

$$\sum_i \frac{z_i (K_i - 1)}{1 + \beta (K_i - 1)} = 0 .$$

Components with $z_i = 0$ are allowed. The K-values are given numbers; how they arise from a thermodynamic model is outside this
result, and so are negative flashes with $\beta \notin [0, 1]$.

For a finite component set, the objective equals $\sum_i y_i - \sum_i x_i$. The feed balance gives $(1-\beta)\sum_i x_i+\beta\sum_i y_i=1$, so if the sums coincide, both are one. This argument uses neither $\beta>0$ nor $\beta<1$.

## Sources

- M. Adewumi, *Phase Relations in Reservoir Engineering*, LibreTexts, Section 13.2, the Rachford–Rice objective function, <https://eng.libretexts.org/Bookshelves/Chemical_Engineering/Phase_Relations_in_Reservoir_Engineering_(Adewumi)/13%3A_Elementary_Vapor-Liquid_Equilibrium_II/13.02%3A_Objective_Function_and_Newton-Raphson_Procedure>.
