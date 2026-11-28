# Equilibria and fear-driven bifurcations in an SIP model with prey aggregation

**Model.** Susceptible prey $S$, infected prey $I$ and predators $P$ satisfy

$$\begin{aligned}
\dot S&=\frac{b_0S}{1+k_1P}\Big(1-\frac{S+I}{K}\Big)-a_0S-d_0S^rP-\frac{e_0SI}{1+k_2P},\\
\dot I&=-a_1I+\frac{e_0SI}{1+k_2P}-d_1IP,\\
\dot P&=-a_2P+d_2S^rP+d_3IP,
\end{aligned}$$

with positive parameters: prey birth rate $b_0$, carrying capacity $K$, death rates $a_0,a_1,a_2$, transmission rate $e_0$, attack rates $d_0,d_1$, conversion efficiencies $d_2,d_3$, aggregation exponent $r\in(0,1)$ (predation on $S^r$, modelling herd-like aggregation of susceptibles), and the *dual fear* parameters $k_1$ (fear-reduced prey reproduction) and $k_2$ (fear-reduced disease transmission).

**Statements.**

1. *(Well-posedness.)* Solutions with nonnegative initial data stay nonnegative; if $d_2<d_0$ and $d_3<d_1$, solutions with positive initial data are uniformly bounded.
2. *(Susceptible-only equilibrium.)* $E_1=(S_1,0,0)$ with $S_1=K(1-a_0/b_0)$ exists when $b_0>a_0$ and is locally asymptotically stable when

    $$a_1>e_0K\Big(1-\frac{a_0}{b_0}\Big)\quad\text{and}\quad a_2>d_2\Big(K-\frac{a_0K}{b_0}\Big)^{r},$$

    i.e. when neither the infection nor the predator can invade the disease-free, predator-free prey population. The predator-free state $E_2$, the infection-free state $E_3$ and the coexistence state $E_4$ are stable under Routh-Hurwitz conditions on their Jacobians; at the extinction state $E_0$ the vector field is not $C^1$ (the aggregation term $S^r$ is not differentiable at $S=0$), so linearization does not apply there.

3. *(Fear-driven bifurcations.)* At the coexistence equilibrium $E_4$, with characteristic polynomial $\lambda^3+\Psi_1\lambda^2+\Psi_2\lambda+\Psi_3$:
   - as $k_1$ or $k_2$ crosses a critical value $k^*$ with $\det J(E_4)=0$ and $\mathrm{tr}\,J(E_4)<0$, a saddle-node bifurcation occurs;
   - as $k_1$ or $k_2$ crosses $k^H$ where $\Psi_1>0$, $\Psi_3>0$, $\Psi_1\Psi_2=\Psi_3$ and $\frac{d}{dk}(\Psi_1\Psi_2-\Psi_3)\ne0$, a Hopf bifurcation produces periodic orbits.
   Numerically, two-parameter continuations show zero-Hopf and saddle-node-transcritical points, and increasing fear can stabilize oscillatory coexistence.

## Expansion

Nonnegativity follows because each right-hand side is proportional to its own variable, and boundedness from a weighted sum $S+I+P$ whose derivative is controlled once conversion efficiencies are below attack rates. At $E_1$ the Jacobian is triangular: the prey eigenvalue is $a_0-b_0<0$, the infection eigenvalue is $e_0S_1-a_1$ and the predator eigenvalue is $d_2S_1^r-a_2$, which gives the two invasion conditions. For the cubic characteristic polynomial, Routh-Hurwitz stability means $\Psi_1,\Psi_3>0$ and $\Psi_1\Psi_2>\Psi_3$; loss of the last inequality with a transversal crossing is a Hopf bifurcation, and a zero eigenvalue ($\Psi_3=\det(-J)=0$) with the remaining eigenvalues in the left half-plane gives a saddle-node, verified by Sotomayor's conditions.

## Sources

- Kwadwo Antwi-Fordjour, Sarah P. Westmoreland and Kendall H. Bearden, "Dual fear phenomenon in an eco-epidemiological model with prey aggregation", The European Physical Journal Plus 139 (2024), 518, <https://doi.org/10.1140/epjp/s13360-024-05324-7>; numbering as in arXiv:2308.06772: model (Section 2), Theorems 3.1, 3.2, 4.1-4.4 and 5.1-5.4.
